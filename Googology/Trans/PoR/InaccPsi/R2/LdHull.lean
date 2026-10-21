import Googology.Trans.PoR.InaccPsi.R2.MxLayB

/-!
# The hull below `Ω₂` at every code: the atoms `ψ_{Ω₂}(a)`, `a ∈ Cl(A, ρ)`, `a < A`, and their readings

`ψ = S.psi`, `A_η = Ω_ω + θ·η`, `ρ_λ = υ_λ = ψ_{Ω₁}(A_{η_λ})`, `H_λ = Cl(A_{η_λ}, ρ_λ)` (`Cd.cdHull`),
`Θ_λ(m) = otp(H_λ ∩ m)` (`Cd.cdTheta`), `K_j` the layers (`Mx.mxKs`), `GxCl Z At` the codes over `Z` with the
atoms `At`, `gxTh Z At` their order type (`R2.MxGx`).

* `ldAt S A ρ = {ψ_{Ω₂}(a) | a ∈ Cl(A, ρ), a < A}` (**all the atoms of the hull below `Ω₂`**), `ldAtR S λ` its value
  at a restart, `ldAt_GxAt`;
* `ldHullG_iff` (**`Cl(A, ρ) ∩ Ω₂` is the set of codes over `ρ` with the atoms `ldAt S A ρ`**, whenever
  `Cl(A, ρ) ∩ Ω₁ ⊆ ρ`), `ldHull_iff` (at every named restart), `ldTheta` (**`Θ_λ(m) = gxTh ρ_λ (ldAtR λ) m` for every
  `m ≤ Ω₂`**, so for every code `m < P' < Ω₂`, `π`-codes included);
* `ldAtom_le`, `ldAtom_ge` (**the reading of an atom `s` is the least strongly critical ordinal above `Z` and above
  the readings of the atoms below `s`**: the order type at level 2 is the order type of the atoms);
* `ldLay_iff`, `ldLay_th` (the codes and readings of the layer `j` are those of the full hull below `K_j`);
* `ldMod_add_lt`, `ldMod_add_ge`, `ldMod_prin` (the countable remainder `x % Ω₁`), `ldPsi1_le` (**`ψ_{Ω₁}(a) ≤ T` for
  a countable strongly critical `T` if `ψ_{Ω₁}(e) < T` for every `e < a` with `e % Ω₁ < T`**: every member of
  `Cl(a, T)` has its countable remainder below `T`).

No new axiom.  New definitions: `ldAt`, `ldAtR`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ld

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf
  Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- **The atoms of `Cl(A, ρ)` below `Ω₂`**: `ψ_{Ω₂}(a)` for `a ∈ Cl(A, ρ)`, `a < A`. -/
def ldAt (S : InaccSeq.{0}) (A ρ : Ordinal.{0}) : Set Ordinal.{0} :=
  {s | ∃ a, a ∈ S.CSet A ρ ∧ a < A ∧ s = S.psi a (Om (1 + 1))}

/-- The atoms of the hull at a restart `λ`. -/
def ldAtR (S : InaccSeq.{0}) (l : Ordinal.{0}) : Set Ordinal.{0} :=
  ldAt S (ConjT.Aη S (cdEta S l)) (upsilon l)

theorem ldAt_GxAt (A ρ : Ordinal.{0}) : GxAt (ldAt S A ρ) := by
  rintro s ⟨a, -, -, rfl⟩
  exact ⟨SC_psi (InR_Om_succ 1) a, (psiS_bounds a 1).1⟩

/-! ## The hull below `Ω₂` -/

/-- **`Cl(A, ρ) ∩ Ω₂` is the set of codes over `ρ` with the atoms `ldAt S A ρ`** (when `Cl(A, ρ) ∩ Ω₁ ⊆ ρ`). -/
theorem ldHullG_iff {A ρ x : Ordinal.{0}} (hρ0 : 0 < ρ) (key : ∀ y ∈ S.CSet A ρ, y < Om 1 → y < ρ)
    (hx2 : x < Om (1 + 1)) : x ∈ S.CSet A ρ ↔ GxCl ρ (ldAt S A ρ) x := by
  constructor
  · intro hx
    revert hx2
    have hx' := hx
    induction hx with
    | small h => exact fun _ => GxCl.small h
    | zero => exact fun _ => GxCl.zero hρ0
    | inacc n => exact fun h => absurd (h.trans (mxOm2_lt_I n)) (lt_irrefl _)
    | inaccW => exact fun h => absurd (h.trans mxOm2_lt_Iw) (lt_irrefl _)
    | @add x y hx1 hy1 ihx ihy =>
      intro h
      exact GxCl.add (ihx hx1 (lt_of_le_of_lt le_self_add h)) (ihy hy1 (lt_of_le_of_lt le_add_self h))
    | @phi x y hx1 hy1 ihx ihy =>
      intro h
      exact GxCl.phi (ihx hx1 (lt_of_le_of_lt (left_le_veblen x y) h))
        (ihy hy1 (lt_of_le_of_lt (right_le_veblen x y) h))
    | @om x _ _ =>
      intro h
      have h2 : x < 1 + 1 := Om_lt_Om.1 h
      rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
      · rw [Order.lt_one_iff] at h0; rw [h0, Om_zero]; exact GxCl.zero hρ0
      · rw [h1]; exact GxCl.om
    | @coll π e hπ _ he1 _ _ =>
      intro h
      rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
      · exfalso
        have h2 : Om (1 + 1 : Ordinal.{0}) < S.psi e.1 (S.I n) :=
          lt_psi_of_mem (InR_I n) (mxOm2_mem _ _) (mxOm2_lt_I n)
        exact absurd (h2.trans h) (lt_irrefl _)
      rcases eq_or_ne s 0 with rfl | hs0
      · rw [zero_add] at hx' ⊢
        exact GxCl.small (key _ hx' (psi_lt Low.InR_Om_one _))
      rcases eq_or_ne s 1 with rfl | hs1
      · exact GxCl.atom ⟨e.1, he1, e.2, rfl⟩
      · exfalso
        have h2s : 1 + 1 ≤ s := Order.add_one_le_of_lt (lt_of_le_of_ne
          (Order.one_le_iff_ne_zero.2 hs0) (Ne.symm hs1))
        have h2 := (Om_lt_psiS (S := S) e.1 s).2 h2s
        exact absurd (h2.trans h) (lt_irrefl _)
  · intro hx
    clear hx2
    induction hx with
    | small h => exact CSet.of_lt h
    | om => exact CSet.Om_mem (CSet.one_mem _ _)
    | atom hs =>
      obtain ⟨a, ha, haA, rfl⟩ := hs
      exact CSet.psi_mem haA (InR_Om_succ 1) (mxOm2_mem _ _) ha
    | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
    | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-- **At every named restart the hull below `Ω₂` is the set of codes over `ρ_λ` with the atoms `ldAtR λ`.** -/
theorem ldHull_iff {l ηx x : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hx2 : x < Om (1 + 1)) : x ∈ cdHull S l ↔ GxCl (upsilon l) (ldAtR S l) x := by
  have hpv := cdEta_pv (S := S) hl.1 hX
  have hρ : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l := hpv
  exact ldHullG_iff (mvUps_pos hl) (fun y hy hy1 => by
    rw [← hρ] at hy ⊢; exact lt_psi_of_mem Low.InR_Om_one hy hy1) hx2

/-- **`Θ_λ(m) = gxTh ρ_λ (ldAtR λ) m` for every `m ≤ Ω₂`** at a named restart. -/
theorem ldTheta {l ηx m : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hm : m ≤ Om (1 + 1)) : cdTheta S l m = gxTh (upsilon l) (ldAtR S l) m :=
  ggOtp_congr m fun _ hx => ldHull_iff hl hX (hx.trans_le hm)

/-! ## The readings of the atoms -/

/-- **The reading of `s` is at most every strongly critical `X > Z` above the readings of the atoms below `s`.** -/
theorem ldAtom_le {Z s X : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)
    (hX : SC X) (hZX : Z < X) (hatom : ∀ t ∈ At, t < s → gxTh Z At t < X) : gxTh Z At s ≤ X := by
  have hbd := mxGx_bound hZ hZ1 hAt hX hZX hatom
  unfold gxTh
  rw [cdOtp_eq]
  refine ciSup_le' fun c => ?_
  split_ifs with hc
  · exact Order.add_one_le_of_lt (hbd c.1 hc c.2)
  · exact zero_le

/-- **The reading of an atom `s` is strongly critical, above `Z` and above the readings of the atoms below `s`.** -/
theorem ldAtom_ge {Z s : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)
    (hs : s ∈ At) :
    SC (gxTh Z At s) ∧ Z < gxTh Z At s ∧ ∀ t ∈ At, t < s → gxTh Z At t < gxTh Z At s := by
  refine ⟨gxTh_SC hZ hAt (hAt s hs).1 (hZ1.trans (hAt s hs).2), ?_,
    fun t ht hts => gxTh_lt (GxCl.atom ht) hts⟩
  have := gxTh_lt (Z := Z) (At := At) GxCl.om (hAt s hs).2
  rwa [gxTh_Om1 hZ hZ1 hAt] at this

/-! ## The layers inside the full hull -/

/-- The codes of the layer `j` are the codes of the full hull below `K_j`. -/
theorem ldLay_iff {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (j : ℕ)
    {x : Ordinal.{0}} (hx : x < mxKs S j) :
    GxCl (upsilon l) (ldAtR S l) x ↔ GxCl (upsilon l) (mxAtL S (upsilon l) j) x :=
  (ldHull_iff hl hX (hx.trans (mxKs_lt_Om2 j))).symm.trans (mxHullL_iff hl hX j x hx)

/-- The readings of the layer `j` are those of the full hull below `K_j`. -/
theorem ldLay_th {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (j : ℕ)
    {m : Ordinal.{0}} (hm : m ≤ mxKs S j) :
    gxTh (upsilon l) (ldAtR S l) m = gxTh (upsilon l) (mxAtL S (upsilon l) j) m := by
  rw [← ldTheta hl hX (hm.trans (mxKs_lt_Om2 j).le), mxThetaL hl hX j hm]

/-! ## The countable remainder `x % Ω₁` -/

theorem ldOm1_prin : IsPrincipal (· + ·) (Om (1 : Ordinal.{0})) := Ph.ph_SC_Om1.isPrincipal

/-- `(x + y) % Ω₁ = x % Ω₁ + y` for `y < Ω₁`. -/
theorem ldMod_add_lt (x : Ordinal.{0}) {y : Ordinal.{0}} (hy : y < Om 1) :
    (x + y) % Om 1 = x % Om 1 + y := by
  have hr : x % Om 1 < Om 1 := Ordinal.mod_lt x (Om_pos one_ne_zero).ne'
  have e : x + y = Om 1 * (x / Om 1) + (x % Om 1 + y) := by
    conv_lhs => rw [← Ordinal.div_add_mod x (Om 1)]
    rw [add_assoc]
  rw [e, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (ldOm1_prin hr hy)]

/-- `(x + y) % Ω₁ = y % Ω₁` for `y ≥ Ω₁`. -/
theorem ldMod_add_ge (x : Ordinal.{0}) {y : Ordinal.{0}} (hy : Om 1 ≤ y) :
    (x + y) % Om 1 = y % Om 1 := by
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  set q := y / Om 1 with hq
  set r' := y % Om 1 with hr'
  have hy' : y = Om 1 * q + r' := (Ordinal.div_add_mod y (Om 1)).symm
  have hq0 : q ≠ 0 := by
    intro h0
    have : y < Om 1 := by
      rw [hy', h0, mul_zero, zero_add]; exact Ordinal.mod_lt y hΩ0
    exact absurd hy (not_le.2 this)
  have habs : x % Om 1 + Om 1 * q = Om 1 * q := by
    refine Ordinal.add_of_omega0_opow_le (b := Om 1) ?_ ?_
    · rw [Bt.Om1_opow]; exact Ordinal.mod_lt x hΩ0
    · rw [Bt.Om1_opow]; exact le_mul_left (Om 1) (pos_iff_ne_zero.2 hq0)
  have e : x + y = Om 1 * (x / Om 1 + q) + r' := by
    conv_lhs => rw [← Ordinal.div_add_mod x (Om 1), hy']
    rw [mul_add, add_assoc (Om 1 * (x / Om 1)), ← add_assoc (x % Om 1), habs, add_assoc]
  rw [e, Ordinal.mul_add_mod_self]
  exact Ordinal.mod_eq_of_lt (Ordinal.mod_lt y hΩ0)

/-- An additive principal `p ≥ Ω₁` is a multiple of `Ω₁`. -/
theorem ldDvd_of_prin {p : Ordinal.{0}} (hp : IsPrincipal (· + ·) p) (h1 : Om 1 ≤ p) : Om 1 ∣ p := by
  rcases isPrincipal_add_iff_zero_or_omega0_opow.1 hp with h0 | ⟨γ, rfl⟩
  · exact absurd (h0 ▸ h1) (not_le.2 (Om_pos one_ne_zero))
  · have hγ : Om 1 ≤ γ := by
      rw [← Bt.Om1_opow] at h1; exact (opow_le_opow_iff_right one_lt_omega0).1 h1
    rw [← Bt.Om1_opow]; exact opow_dvd_opow ω hγ

/-- **The remainder of an additive principal is itself or `0`.** -/
theorem ldMod_prin {p : Ordinal.{0}} (hp : IsPrincipal (· + ·) p) :
    (p < Om 1 ∧ p % Om 1 = p) ∨ p % Om 1 = 0 := by
  rcases lt_or_ge p (Om 1) with h | h
  · exact Or.inl ⟨h, Ordinal.mod_eq_of_lt h⟩
  · exact Or.inr (Ordinal.mod_eq_zero_of_dvd (ldDvd_of_prin hp h))

/-- **`ψ_{Ω₁}(a) ≤ T`** for a countable strongly critical `T`, if `ψ_{Ω₁}(e) < T` for every `e < a` whose countable
remainder `e % Ω₁` is below `T`. -/
theorem ldPsi1_le {a T : Ordinal.{0}} (hT : SC T)
    (hcoll : ∀ e, e < a → e % Om 1 < T → S.psi e (Om 1) < T) : S.psi a (Om 1) ≤ T := by
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have prin : ∀ {p : Ordinal.{0}}, IsPrincipal (· + ·) p → (p < Om 1 → p < T) → p % Om 1 < T := by
    intro p hp h
    rcases ldMod_prin hp with ⟨hp1, e⟩ | e
    · rw [e]; exact h hp1
    · rw [e]; exact hT.1
  have key : ∀ x ∈ S.CSet a T, x % Om 1 < T := by
    intro x hx
    induction hx with
    | small h => exact (Ordinal.mod_le _ _).trans_lt h
    | zero => rw [Ordinal.zero_mod]; exact hT.1
    | inacc n =>
      exact prin (SC_I (S := S) n).isPrincipal fun h => absurd h (not_lt.2 (gg_Om1_lt_I S n).le)
    | inaccW =>
      exact prin (SC_Iw (S := S)).isPrincipal fun h => absurd h (not_lt.2 (gg_Om1_lt_Iw S).le)
    | @add x y _ _ ihx ihy =>
      rcases lt_or_ge y (Om 1) with hy | hy
      · rw [ldMod_add_lt x hy]
        have hyT : y < T := by rwa [Ordinal.mod_eq_of_lt hy] at ihy
        exact hT.isPrincipal ihx hyT
      · rw [ldMod_add_ge x hy]; exact ihy
    | @phi x y _ _ ihx ihy =>
      refine prin (Ph.ph_veblen_prin x y) fun h => ?_
      have hx1 : x < Om 1 := lt_of_le_of_lt (left_le_veblen x y) h
      have hy1 : y < Om 1 := lt_of_le_of_lt (right_le_veblen x y) h
      rw [Ordinal.mod_eq_of_lt hx1] at ihx
      rw [Ordinal.mod_eq_of_lt hy1] at ihy
      exact hT.2 x ihx y ihy
    | @om x _ _ =>
      rcases eq_or_ne x 0 with rfl | hx0
      · rw [Om_zero, Ordinal.zero_mod]; exact hT.1
      · refine prin (Om_isPrincipal hx0) fun h => ?_
        exact absurd (mxOm_lt_one h) hx0
    | @coll π e hπ _ _ _ ihe =>
      refine prin (SC_psi hπ e.1).isPrincipal fun h => ?_
      have hπ1 : π = Om 1 := by
        by_contra hne
        exact absurd h (not_lt.2 (mxOm1_le_psi hπ hne))
      subst hπ1
      exact hcoll e.1 e.2 ihe
  refine psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) fun x hx hx1 => ?_
  have := key x hx
  rwa [Ordinal.mod_eq_of_lt hx1] at this

end Googology.Trans.PoR.InaccPsi.R2.Ld
