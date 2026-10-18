import Googology.Trans.PoR.InaccPsi.R2.PhLy
import Googology.Trans.PoR.InaccPsi.R2.LzWS

/-!
# The systems `lzZ`, `lzVs`, `lzWs K`: terms for every code below the code of the top

The tops and their codes (`Θ_y(code) = top(y)` at every strongly critical `y < Ω₁`):

* `lzZ`: `e_y(y) = ϑʸ(Ω₁ + B(y) + y) = φ(1, B(y) + 1 + y)`, code `phZT = φ(1, phB + 1 + Ω₁)` (`phLzE_eq`:
  `e_c(y) = φ(1, B(y) + 1 + c)` for `c ≤ y`, from the enumeration `Lz.lzE_enum`);
* `lzVs`: `B₁(y) = B(B(y)) = φ(ω, y + 2)`, code `phV = φ(ω, Ω₁ + 2)`;
* `lzWs K`: `y_K(y) = ϑʸ(Ω₁·ω + K) = φ(ω, y + 1 + K)`, code `phW K = φ(ω, Ω₁ + 1 + K)` (`phLzY_eq`).

* `phShape` (a nonzero code over a strongly critical `Z` is a sum of two smaller codes, `ω^L` with a smaller code
  `L`, or an `ε`-number), `phEpsDec` (an `ε`-number code `c > Ω₁` is `φ(ω, γ)`, `φ_k(b)` with `1 ≤ k < ω`, `b > Ω₁`,
  `b < φ_k(b)`, or `φ(a, b)` with `a > ω`, all with codes), `phTh_th` (`ϑʸ(Ω₁·k + ind(Θ_y(b))) = Θ_y(φ_k(b))`);
* `phPoly_lzZ`, `phPoly_lzV`, `phPoly_lzW` (**`GgPoly` of `lzZ`, `lzVs`, `lzWs K` up to the codes of their tops**),
  `phTh_ZT`, `phTh_V`, `phTh_W`;
* `phLzZ`, `phLzV`, `phLzW` (**THEOREM UNI** for them).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ph

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lz

variable {S : InaccSeq.{0}} {Z : Ordinal.{0}}

/-! ## The shape of a code -/

/-- A nonzero code is a sum of two smaller codes, a power `ω^L` of a smaller code, or an `ε`-number. -/
theorem phShape (hZ : SC Z) {c : Ordinal.{0}} (hc : GgCl Z c) (hc0 : c ≠ 0) :
    (∃ u v, GgCl Z u ∧ GgCl Z v ∧ u < c ∧ v < c ∧ c = u + v) ∨ (∃ L, GgCl Z L ∧ L < c ∧ c = ω ^ L) ∨
      ω ^ c = c := by
  obtain ⟨hsub, hlog⟩ := ggDec hZ c hc
  have hw : GgCl Z (ω ^ log ω c) := GgCl.opow hZ.1 hlog
  have hwc : ω ^ log ω c ≤ c := opow_log_le_self ω hc0
  rcases hwc.lt_or_eq with hwc' | hwc'
  · exact Or.inl ⟨_, _, hw, hsub _ hw hwc, hwc', ph_sub_log_lt hc0, (Ordinal.add_sub_cancel_of_le hwc).symm⟩
  rcases (log_le_self ω c).lt_or_eq with hL | hL
  · exact Or.inr (Or.inl ⟨_, hlog, hL, hwc'.symm⟩)
  · right; right; conv_lhs => rw [← hL]
                              exact hwc'

/-- **An `ε`-number code above `Ω₁`**: `φ(ω, γ)`, `φ_k(b)` (`1 ≤ k < ω`, `Ω₁ < b < φ_k(b)`), or `φ(a, b)` with
`a > ω`. -/
theorem phEpsDec (hZ : SC Z) {c : Ordinal.{0}} (hc : GgCl Z c) (hc1 : Om 1 < c) (hcE : ω ^ c = c) :
    (∃ γ, GgCl Z γ ∧ Om 1 < γ ∧ γ < c ∧ c = veblen ω γ) ∨
    (∃ k : ℕ, 1 ≤ k ∧ ∃ b, GgCl Z b ∧ Om 1 < b ∧ b < veblen (k : Ordinal.{0}) b ∧
      c = veblen (k : Ordinal.{0}) b) ∨
    (∃ a b, ω < a ∧ b < c ∧ c = veblen a b) := by
  have hdec : veblen (invVeblen₁ c) (invVeblen₂ c) = c := by rw [veblen_invVeblen₁_invVeblen₂, hcE]
  have hb1 : invVeblen₂ c < c := by have := invVeblen₂_lt c; rwa [hcE] at this
  obtain ⟨ha, hb⟩ := phDec hZ.1 hc _ _ hdec hb1
  set a := invVeblen₁ c with hadef
  set b := invVeblen₂ c with hbdef
  have hSC1 := ph_SC_Om1
  have hbO : ∀ a', a' < Om 1 → veblen a' b = c → Om 1 < b := by
    intro a' ha' e
    by_contra hle
    push Not at hle
    have h3 := (veblen_le_veblen_iff_right (o := a')).2 hle
    rw [e, hSC1.veblen_right ha'] at h3
    exact absurd hc1 (not_lt.2 h3)
  rcases lt_trichotomy a ω with h | h | h
  · obtain ⟨k, hk⟩ := lt_omega0.1 h
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exfalso
        rw [hk, h0, Nat.cast_zero, veblen_zero_apply] at hdec
        have e := hcE
        rw [← hdec] at e
        have e2 := (opow_right_inj one_lt_omega0).1 e
        rw [← hdec, e2] at hb1
        exact lt_irrefl _ hb1
      · exact h0
    rw [hk] at hdec
    refine Or.inr (Or.inl ⟨k, hk1, b, hb, hbO _ ((natCast_lt_omega0 k).trans (ph_omega_lt hSC1)) hdec,
      by rw [hdec]; exact hb1, hdec.symm⟩)
  · rw [h] at hdec
    exact Or.inl ⟨b, hb, hbO _ (ph_omega_lt hSC1) hdec, hb1, hdec.symm⟩
  · exact Or.inr (Or.inr ⟨a, b, h, hb1, hdec.symm⟩)

/-- `ϑʸ(Ω₁·k + ind(Θ_y(b))) = Θ_y(φ_k(b))`. -/
theorem phTh_th {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) {k : ℕ} (hk : 1 ≤ k) {b : Ordinal.{0}}
    (hb : GgCl y b) (hbO : Om 1 < b) (hbv : b < veblen (k : Ordinal.{0}) b) (hT : phInd k y (ggTh y b) ∈ Tset y)
    (hη1 : phInd k y (ggTh y b) < Om1) :
    vt y (Om1 * (k : Ordinal.{0}) + phInd k y (ggTh y b)) = ggTh y (veblen (k : Ordinal.{0}) b) := by
  have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
  have hyb : y < ggTh y b := by
    have := ggTh_lt (GgCl.om (Z := y)) hbO (y := y); rwa [ggTh_Om1 hy hy1] at this
  have hbP : ¬ VzP (k + 1) (ggTh y b) := by
    intro hP
    have h1 := ggTh_lt hb hbv
    rw [phTh_veblen_nat hy k hb, vzP_succ.1 hP] at h1
    exact lt_irrefl _ h1
  rw [phTh_veblen_nat hy k hb, phLev hy hy1' hk _ hyb hbP hT hη1]

/-! ## The atoms of the tops -/

/-- `B(φ(ω, γ)) = φ(ω, γ + 1)`. -/
theorem ph_VzB_veblen {γ : Ordinal.{0}} (h1 : veblen ω γ < Om1) : VzB (veblen ω γ) = veblen ω (γ + 1) := by
  have hE : InE (veblen ω γ) := gg_veblen_eps omega0_ne_zero
  obtain ⟨⟨δ, hδ⟩, hlt, hmin⟩ := vzB_omega hE h1
  apply le_antisymm
  · exact hmin _ ⟨_, rfl⟩ (veblen_lt_veblen_iff_right.2 (lt_add_one γ))
  · rw [← hδ]
    refine veblen_le_veblen_iff_right.2 (Order.add_one_le_of_lt ?_)
    rw [← hδ] at hlt
    exact veblen_lt_veblen_iff_right.1 hlt

theorem ph_VzB_eq {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : VzB y = veblen ω (y + 1) := by
  rw [← phTh_B hy hy1, phB, phTh_veblen_omega hy (ph_cl_Om1_one hy), phTh_Om1_one hy hy1]

/-- **`y_K(y) = φ(ω, y + 1 + K)`**. -/
theorem phLzY_eq {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : ∀ K : ℕ, lzY y K = veblen ω (y + 1 + K) := by
  have hyE : InE y := gg_SC_eps hy
  have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
  intro K
  induction K with
  | zero => rw [lzY_zero hyE hy1', Nat.cast_zero, add_zero, ph_VzB_eq hy hy1]
  | succ K ih =>
    rw [lzY_succ hyE hy1' K, ih, ph_VzB_veblen (by rw [← ih]; exact (lzY_facts hyE hy1' K).2.2.1), Nat.cast_succ,
      add_assoc]

/-- **`e_c(y) = φ(1, B(y) + 1 + c)`** for `c ≤ y`. -/
theorem phLzE_eq {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) :
    ∀ c, c ≤ y → lzE y c = veblen 1 (VzB y + 1 + c) := by
  have hyE : InE y := gg_SC_eps hy
  have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
  have hBfix : veblen 1 (VzB y) = VzB y := by
    obtain ⟨⟨γ, hγ⟩, -, -⟩ := vzB_omega hyE hy1'
    rw [← hγ]; exact veblen_veblen_of_lt one_lt_omega0 γ
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcy
  obtain ⟨-, -, -, -, -, heE, -, hBc⟩ := lzE_facts hyE hy1' hcy
  have hBe : VzB y < lzE y c := lt_of_le_of_lt le_self_add hBc
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    have hvE : InE (veblen 1 (VzB y + 1 + c)) := gg_veblen_eps one_ne_zero
    have hBv : VzB y < veblen 1 (VzB y + 1 + c) :=
      (lt_add_one _).trans_le (le_self_add.trans (right_le_veblen _ _))
    obtain ⟨c', hc', e⟩ := lzE_enum hyE hy1' hcy hvE hBv hlt
    rw [IH c' hc' (hc'.le.trans hcy)] at e
    exact absurd e (veblen_lt_veblen_iff_right.2 ((add_lt_add_iff_left _).2 hc')).ne'
  · obtain ⟨γ, hγ⟩ := (vzP_one (a := lzE y c)).2 heE
    rw [Nat.cast_one] at hγ
    rw [← hγ]
    refine veblen_le_veblen_iff_right.2 ?_
    by_contra hlt
    push Not at hlt
    have hBγ : VzB y < γ := by
      by_contra hle
      push Not at hle
      have h2 := (veblen_le_veblen_iff_right (o := (1 : Ordinal.{0}))).2 hle
      rw [hBfix, hγ] at h2
      exact absurd hBe (not_lt.2 h2)
    obtain ⟨c', hc'⟩ := exists_add_of_le (Order.add_one_le_of_lt hBγ)
    rw [hc'] at hlt hγ
    have hc'c : c' < c := (add_lt_add_iff_left _).1 hlt
    have h3 := lzE_strict hyE hy1' hc'c hcy
    rw [IH c' hc'c (hc'c.le.trans hcy), hγ] at h3
    exact lt_irrefl _ h3

/-! ## The codes of the tops -/

/-- The code `φ(1, phB + 1 + Ω₁)` of the top `e_x(x)` of `lzZ`. -/
noncomputable def phZT : Ordinal.{0} := veblen 1 (phB + 1 + Om 1)

/-- The code `φ(ω, Ω₁ + 2)` of the top `B₁(x)` of `lzVs`. -/
noncomputable def phV : Ordinal.{0} := veblen ω (Om 1 + 1 + 1)

/-- The code `φ(ω, Ω₁ + 1 + K)` of the top `y_K(x)` of `lzWs K`. -/
noncomputable def phW (K : ℕ) : Ordinal.{0} := veblen ω (Om 1 + 1 + K)

theorem ph_cl_one (hZ : SC Z) : GgCl Z 1 := GgCl.small (gg_one_lt_of_SC hZ)

theorem ph_cl_ZT (hZ : SC Z) : GgCl Z phZT :=
  GgCl.phi (ph_cl_one hZ) (GgCl.add (GgCl.add (ph_cl_B hZ) (ph_cl_one hZ)) GgCl.om)

theorem ph_cl_V (hZ : SC Z) : GgCl Z phV :=
  GgCl.phi (GgCl.small (ph_omega_lt hZ)) (GgCl.add (ph_cl_Om1_one hZ) (ph_cl_one hZ))

theorem ph_cl_W (hZ : SC Z) (K : ℕ) : GgCl Z (phW K) :=
  GgCl.phi (GgCl.small (ph_omega_lt hZ)) (GgCl.add (ph_cl_Om1_one hZ) (ph_cl_nat hZ K))

theorem phTh_ZT {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : ggTh y phZT = lzE y y := by
  have h1 := gg_one_lt_of_SC hy
  unfold phZT
  rw [phTh_phi hy _ (ph_cl_one hy) _ (GgCl.add (GgCl.add (ph_cl_B hy) (ph_cl_one hy)) GgCl.om),
    ggTh_small h1.le, ggTh_add hy (GgCl.add (ph_cl_B hy) (ph_cl_one hy)), ggTh_add hy (ph_cl_B hy),
    ggTh_small h1.le, phTh_B hy hy1, ggTh_Om1 hy hy1, phLzE_eq hy hy1 y le_rfl]

theorem phTh_V {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : ggTh y phV = VzB1 y := by
  have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
  have h1 := gg_one_lt_of_SC hy
  unfold phV
  rw [phTh_veblen_omega hy (GgCl.add (ph_cl_Om1_one hy) (ph_cl_one hy)), ggTh_add hy (ph_cl_Om1_one hy),
    phTh_Om1_one hy hy1, ggTh_small h1.le, lzB1_eq (gg_SC_eps hy) hy1', ph_VzB_eq hy hy1,
    ph_VzB_veblen (by rw [← ph_VzB_eq hy hy1]; exact xt_B_lt_Om1 (gg_SC_eps hy) hy1')]

theorem phTh_W {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) (K : ℕ) : ggTh y (phW K) = lzY y K := by
  unfold phW
  rw [phTh_veblen_omega hy (GgCl.add (ph_cl_Om1_one hy) (ph_cl_nat hy K)), ggTh_add hy (ph_cl_Om1_one hy),
    phTh_Om1_one hy hy1, phTh_nat hy, phLzY_eq hy hy1 K]

theorem ph_eps_gt {c : Ordinal.{0}} (hcE : ω ^ c = c) (hc1 : Om 1 < c) (n : ℕ) : Om 1 + n < c := by
  have hp : IsPrincipal (· + ·) c := by rw [← hcE]; exact isPrincipal_add_omega0_opow c
  exact hp hc1 ((natCast_lt_omega0 n).trans_le ((ph_omega_lt ph_SC_Om1).le.trans hc1.le))

/-- An `ε`-number `φ(a, b)` with `a > α` below `φ(α, X)` is below `X`. -/
theorem ph_veblen_lt_of_gt {a b α X : Ordinal.{0}} (ha : α < a) (h : veblen a b < veblen α X) :
    veblen a b < X := by
  rcases veblen_lt_veblen_iff.1 h with ⟨e, -⟩ | ⟨h', -⟩ | ⟨-, h'⟩
  · exact absurd e ha.ne'
  · exact absurd h' (not_lt.2 ha.le)
  · exact h'

/-! ## `lzZ` -/

/-- **`lzZ` has terms for every code below `phZT`.** -/
theorem phPoly_lzZ : GgPoly lzZ phZT := by
  refine phPoly_of_SC fun Z hZ _ => ?_
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcT
  rcases lt_or_ge c phEB with hcE | hcE
  · obtain ⟨t, ht⟩ := phLyTm hZ c hc hcE
    exact ⟨LzTm.ly t, fun y hy hy1 hZy => ht y hy hy1 hZy⟩
  have hp : IsPrincipal (· + ·) phEB := by rw [← ph_EB_eps]; exact isPrincipal_add_omega0_opow _
  have hBO : Om 1 < phB := (lt_add_one _).trans_le (right_le_veblen _ _)
  have hOE : Om 1 < phEB := hBO.trans ph_B_lt_EB
  have hXE : phB + 1 + Om 1 < phEB := hp (hp ph_B_lt_EB ((gg_one_lt_of_SC ph_SC_Om1).trans hOE)) hOE
  have hc1 : Om 1 < c := hOE.trans_le hcE
  have hc0 : c ≠ 0 := (lt_of_le_of_lt zero_le hc1).ne'
  rcases phShape hZ hc hc0 with ⟨u, v, hu, hv, huc, hvc, rfl⟩ | ⟨L, hL, hLc, rfl⟩ | hcE'
  · obtain ⟨s1, hs1⟩ := IH u huc hu (huc.trans hcT)
    obtain ⟨s2, hs2⟩ := IH v hvc hv (hvc.trans hcT)
    refine ⟨LzTm.sm s1 s2, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
    obtain ⟨c2, v2⟩ := hs2 y hy hy1 hZy
    exact ⟨⟨c1, c2⟩, by
      show lzZ.val s1 y + lzZ.val s2 y = _
      rw [v1, v2, ggTh_add hy (hu.mono hZy)]⟩
  · obtain ⟨s1, hs1⟩ := IH L hLc hL (hLc.trans hcT)
    refine ⟨LzTm.pw s1, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
    exact ⟨c1, by show ω ^ lzZ.val s1 y = _; rw [v1, ggTh_opow hy (hL.mono hZy)]⟩
  -- an `ε`-number in `[phEB, phZT)`: `φ(1, phB + 1 + c')`, `c' < Ω₁`
  have hgt : ∀ a b, 1 < a → c = veblen a b → False := fun a b ha e => by
    have h1 := ph_veblen_lt_of_gt ha (e ▸ hcT : veblen a b < veblen 1 (phB + 1 + Om 1))
    rw [← e] at h1
    exact absurd (h1.trans hXE) (not_lt.2 hcE)
  rcases phEpsDec hZ hc hc1 hcE' with ⟨γ, -, -, -, e⟩ | ⟨k, hk, b, hb, -, -, e⟩ | ⟨a, b, ha, -, e⟩
  · exact (hgt ω γ one_lt_omega0 e).elim
  · rcases lt_or_eq_of_le hk with hk' | hk'
    · exact (hgt k b (by exact_mod_cast hk') e).elim
    subst hk'
    rw [Nat.cast_one] at e
    have hb1 : phB + 1 ≤ b := by
      have := hcE; rw [e] at this; exact veblen_le_veblen_iff_right.1 this
    have hb2 : b < phB + 1 + Om 1 := by
      have := hcT; rw [e] at this; exact veblen_lt_veblen_iff_right.1 this
    have hBc := GgCl.add (ph_cl_B hZ) (ph_cl_one hZ)
    have hc' := (ggDec hZ b hb).1 _ hBc hb1
    have hbe : phB + 1 + (b - (phB + 1)) = b := Ordinal.add_sub_cancel_of_le hb1
    have hc'1 : b - (phB + 1) < Om 1 := by
      rw [← hbe] at hb2; exact (add_lt_add_iff_left _).1 hb2
    have hc'Z : b - (phB + 1) < Z := hc'.lt_of_lt_Om1 hZ hc'1
    refine ⟨LzTm.ep (b - (phB + 1)), fun y hy hy1 hZy => ⟨lt_of_lt_of_le hc'Z hZy, ?_⟩⟩
    show lzE y (b - (phB + 1)) = ggTh y c
    rw [phLzE_eq hy hy1 _ (hc'Z.le.trans hZy), e]
    have := phTh_veblen_nat hy 1 (hb.mono hZy)
    rw [Nat.cast_one] at this
    rw [this]
    conv_rhs => rw [← hbe]
    rw [ggTh_add hy (hBc.mono hZy), ggTh_add hy (ph_cl_B hy), phTh_B hy hy1,
      ggTh_small (gg_one_lt_of_SC hy).le, ggTh_small (hc'Z.le.trans hZy)]
  · exact (hgt a b (one_lt_omega0.trans ha) e).elim

/-! ## `lzVs` and `lzWs K` -/

/-- **`lzVs` has terms for every code below `phV`.** -/
theorem phPoly_lzV : GgPoly lzVs phV := by
  refine phPoly_of_SC fun Z hZ _ => ?_
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcT
  rcases lt_trichotomy c (Om 1) with hc1 | hc1 | hc1
  · have hcZ : c < Z := hc.lt_of_lt_Om1 hZ hc1
    exact ⟨LzV.vz (VzTm.cst c), fun y _ _ hZy =>
      ⟨lt_of_lt_of_le hcZ hZy, by show c = ggTh y c; rw [ggTh_small (hcZ.le.trans hZy)]⟩⟩
  · subst hc1
    exact ⟨LzV.vz VzTm.bs, fun y hy hy1 _ => ⟨trivial, by show y = ggTh y (Om 1); rw [ggTh_Om1 hy hy1]⟩⟩
  have hc0 : c ≠ 0 := (lt_of_le_of_lt zero_le hc1).ne'
  rcases phShape hZ hc hc0 with ⟨u, v, hu, hv, huc, hvc, rfl⟩ | ⟨L, hL, hLc, rfl⟩ | hcE'
  · obtain ⟨s1, hs1⟩ := IH u huc hu (huc.trans hcT)
    obtain ⟨s2, hs2⟩ := IH v hvc hv (hvc.trans hcT)
    refine ⟨LzV.sm s1 s2, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
    obtain ⟨c2, v2⟩ := hs2 y hy hy1 hZy
    exact ⟨⟨c1, c2⟩, by
      show lzVs.val s1 y + lzVs.val s2 y = _
      rw [v1, v2, ggTh_add hy (hu.mono hZy)]⟩
  · obtain ⟨s1, hs1⟩ := IH L hLc hL (hLc.trans hcT)
    refine ⟨LzV.pw s1, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
    exact ⟨c1, by show ω ^ lzVs.val s1 y = _; rw [v1, ggTh_opow hy (hL.mono hZy)]⟩
  rcases phEpsDec hZ hc hc1 hcE' with ⟨γ, -, hγ1, -, e⟩ | ⟨k, hk, b, hb, hbO, hbv, e⟩ | ⟨a, b, ha, -, e⟩
  · -- `c = φ(ω, γ)`, so `γ = Ω₁ + 1` and `c = phB`
    have hγ2 : γ < Om 1 + 1 + 1 := by
      have := hcT; rw [e] at this; exact veblen_lt_veblen_iff_right.1 this
    have hγ : γ = Om 1 + 1 := le_antisymm (Order.lt_add_one_iff.1 hγ2) (Order.add_one_le_of_lt hγ1)
    rw [hγ] at e
    refine ⟨LzV.bB, fun y hy hy1 _ => ⟨trivial, ?_⟩⟩
    show VzB y = ggTh y c
    rw [e, ← phB, phTh_B hy hy1]
  · obtain ⟨d, hd, hdb, hdθ⟩ := phIndCode hZ hb hbO hbv
    have hbc : b < c := by rw [e]; exact hbv
    obtain ⟨t, ht⟩ := IH d (hdb.trans_lt hbc) hd ((hdb.trans_lt hbc).trans hcT)
    refine ⟨LzV.th k t, fun y hy hy1 hZy => ?_⟩
    obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
    have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
    refine ⟨⟨hk, ct⟩, ?_⟩
    show vt y (Om1 * (k : Ordinal.{0}) + lzVs.val t y) = ggTh y c
    have hTv : lzVs.val t y ∈ Tset y ∧ lzVs.val t y < Om1 := lzv_T (gg_SC_eps hy) hy1' t ct
    have e1 : lzVs.val t y = phInd k y (ggTh y b) := by rw [vt', hdθ y hy hy1 hZy]
    rw [e1] at hTv ⊢
    rw [e, phTh_th hy hy1 hk (hb.mono hZy) hbO hbv hTv.1 hTv.2]
  · exfalso
    have h1 := ph_veblen_lt_of_gt ha (e ▸ hcT : veblen a b < veblen ω (Om 1 + 1 + 1))
    rw [← e] at h1
    have h2 := ph_eps_gt hcE' hc1 2
    rw [show ((2 : ℕ) : Ordinal.{0}) = 1 + 1 by norm_num, ← add_assoc] at h2
    exact absurd h1 (not_lt.2 h2.le)

/-- **`lzWs K` has terms for every code below `phW K`.** -/
theorem phPoly_lzW (K : ℕ) : GgPoly (lzWs K) (phW K) := by
  refine phPoly_of_SC fun Z hZ _ => ?_
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcT
  rcases lt_trichotomy c (Om 1) with hc1 | hc1 | hc1
  · have hcZ : c < Z := hc.lt_of_lt_Om1 hZ hc1
    exact ⟨LzW.vz (VzTm.cst c), fun y _ _ hZy =>
      ⟨⟨lt_of_lt_of_le hcZ hZy, Nat.zero_le _⟩, by show c = ggTh y c; rw [ggTh_small (hcZ.le.trans hZy)]⟩⟩
  · subst hc1
    exact ⟨LzW.vz VzTm.bs, fun y hy hy1 _ =>
      ⟨⟨trivial, Nat.zero_le _⟩, by show y = ggTh y (Om 1); rw [ggTh_Om1 hy hy1]⟩⟩
  have hc0 : c ≠ 0 := (lt_of_le_of_lt zero_le hc1).ne'
  rcases phShape hZ hc hc0 with ⟨u, v, hu, hv, huc, hvc, rfl⟩ | ⟨L, hL, hLc, rfl⟩ | hcE'
  · obtain ⟨s1, hs1⟩ := IH u huc hu (huc.trans hcT)
    obtain ⟨s2, hs2⟩ := IH v hvc hv (hvc.trans hcT)
    refine ⟨LzW.sm s1 s2, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
    obtain ⟨c2, v2⟩ := hs2 y hy hy1 hZy
    exact ⟨⟨⟨c1.1, c2.1⟩, max_le c1.2 c2.2⟩, by
      show (lzWs K).val s1 y + (lzWs K).val s2 y = _
      rw [v1, v2, ggTh_add hy (hu.mono hZy)]⟩
  · obtain ⟨s1, hs1⟩ := IH L hLc hL (hLc.trans hcT)
    refine ⟨LzW.pw s1, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
    exact ⟨c1, by show ω ^ (lzWs K).val s1 y = _; rw [v1, ggTh_opow hy (hL.mono hZy)]⟩
  rcases phEpsDec hZ hc hc1 hcE' with ⟨γ, -, hγ1, -, e⟩ | ⟨k, hk, b, hb, hbO, hbv, e⟩ | ⟨a, b, ha, -, e⟩
  · -- `c = φ(ω, Ω₁ + 1 + j)`, `j < K`: the atom `y_j`
    have hγ2 : γ < Om 1 + 1 + K := by
      have := hcT; rw [e] at this; exact veblen_lt_veblen_iff_right.1 this
    obtain ⟨δ, hδ⟩ := exists_add_of_le (Order.add_one_le_of_lt hγ1)
    rw [hδ] at hγ2
    have hδK : δ < K := (add_lt_add_iff_left _).1 hγ2
    obtain ⟨j, rfl⟩ := lt_omega0.1 (hδK.trans (natCast_lt_omega0 K))
    have hjK : j < K := by exact_mod_cast hδK
    refine ⟨LzW.yk j, fun y hy hy1 _ => ⟨⟨trivial, hjK⟩, ?_⟩⟩
    show lzY y j = ggTh y c
    rw [e, hδ, ← phW, phTh_W hy hy1]
  · obtain ⟨d, hd, hdb, hdθ⟩ := phIndCode hZ hb hbO hbv
    have hbc : b < c := by rw [e]; exact hbv
    obtain ⟨t, ht⟩ := IH d (hdb.trans_lt hbc) hd ((hdb.trans_lt hbc).trans hcT)
    refine ⟨LzW.th k t, fun y hy hy1 hZy => ?_⟩
    obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
    have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
    refine ⟨⟨⟨hk, ct.1⟩, ct.2⟩, ?_⟩
    show vt y (Om1 * (k : Ordinal.{0}) + (lzWs K).val t y) = ggTh y c
    have hTv : (lzWs K).val t y ∈ Tset y ∧ (lzWs K).val t y < Om1 := lzw_T (gg_SC_eps hy) hy1' t ct.1
    have e1 : (lzWs K).val t y = phInd k y (ggTh y b) := by rw [vt', hdθ y hy hy1 hZy]
    rw [e1] at hTv ⊢
    rw [e, phTh_th hy hy1 hk (hb.mono hZy) hbO hbv hTv.1 hTv.2]
  · exfalso
    have h1 := ph_veblen_lt_of_gt ha (e ▸ hcT : veblen a b < veblen ω (Om 1 + 1 + K))
    rw [← e] at h1
    have h2 := ph_eps_gt hcE' hc1 (1 + K)
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc] at h2
    exact absurd h1 (not_lt.2 h2.le)

/-! ## THEOREM UNI for the `Lz` systems -/

theorem ph_ZT_lt_Gam : phZT < ggGam := ph_lt_Gam (ph_cl_ZT ph_SC_Om1)
theorem ph_V_lt_Gam : phV < ggGam := ph_lt_Gam (ph_cl_V ph_SC_Om1)
theorem ph_W_lt_Gam (K : ℕ) : phW K < ggGam := ph_lt_Gam (ph_cl_W ph_SC_Om1 K)

/-- **THEOREM UNI for `lzZ` up to `phZT`.** -/
theorem phLzZO {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hX : upsilon F < Pv S ηx)
    (he : cdExp (cdEta S F) ≤ phZT) : xtOrec lzZ F = ggTh F (cdExp (cdEta S F)) :=
  ggUni ph_ZT_lt_Gam.le phPoly_lzZ F ηx hF hfix hX he

theorem phLzZ {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hX : upsilon F < Pv S ηx)
    (he : cdExp (cdEta S F) ≤ phZT) : cdTheta S F (cdCode S F) = xtOrec lzZ F :=
  ggUniTh ph_ZT_lt_Gam.le phPoly_lzZ hF hfix hX he

/-- **THEOREM UNI for `lzVs` up to `phV`.** -/
theorem phLzVO {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hX : upsilon F < Pv S ηx)
    (he : cdExp (cdEta S F) ≤ phV) : xtOrec lzVs F = ggTh F (cdExp (cdEta S F)) :=
  ggUni ph_V_lt_Gam.le phPoly_lzV F ηx hF hfix hX he

theorem phLzV {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hX : upsilon F < Pv S ηx)
    (he : cdExp (cdEta S F) ≤ phV) : cdTheta S F (cdCode S F) = xtOrec lzVs F :=
  ggUniTh ph_V_lt_Gam.le phPoly_lzV hF hfix hX he

/-- **THEOREM UNI for `lzWs K` up to `phW K`.** -/
theorem phLzWO (K : ℕ) {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (he : cdExp (cdEta S F) ≤ phW K) : xtOrec (lzWs K) F = ggTh F (cdExp (cdEta S F)) :=
  ggUni (ph_W_lt_Gam K).le (phPoly_lzW K) F ηx hF hfix hX he

theorem phLzW (K : ℕ) {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (he : cdExp (cdEta S F) ≤ phW K) : cdTheta S F (cdCode S F) = xtOrec (lzWs K) F :=
  ggUniTh (ph_W_lt_Gam K).le (phPoly_lzW K) hF hfix hX he

end Googology.Trans.PoR.InaccPsi.R2.Ph
