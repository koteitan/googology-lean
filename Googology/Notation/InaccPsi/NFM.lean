import Googology.Notation.InaccPsi.Struct

/-!
# The least member of the closure above `x`

For the completeness proof the argument `ξ` of a collapse `ψ_κ(ξ)` has to be moved up to

```
M(ξ) = min (Cl(ξ, γ) ∩ [ξ, ∞))          γ = ψ_κ(ξ)
```

`psi_M_eq`: `ψ_κ(M(ξ)) = γ`, and `M_mem_self`: `M(ξ) ∈ Cl(M(ξ), ψ_κ(M(ξ)))`. What is left
is that `M` does not leave a set `T` that `ξ` started in, for `T` closed under the
operations of the closure (`Closed`) — the set of values of normal forms (`Onto.lean`) and
`Cl(α, β)` (here, `MQ_of_mem_CSet`).

`M` is read off the Cantor normal form (`M_mem_of_Good`: the leading summand is kept when it
is in `R = Cl(e, g)`, otherwise `M(x) = M(lead x)`), and on principal summands:

* `M(Ω_a) = Ω_{M(a)}` (`M_Om`, with Pohlers's (172));
* `M(ψ_{I_n}(y)) ∈ {I_n, ψ_{I_n}(M(y))}` (`M_psiI`);
* `M(ψ_{Ω_{s+1}}(y)) ∈ {Ω_{s+1}, Ω_{M(s)}, ψ_{Ω_{s+1}}(M(y))}` (`M_psiS`);
* `M(φ(a, b)) = φ(a, M(b))` if `a ∈ R` (`M_veblen_of_mem`), and
  `M(φ(a, b)) = φ(M(a), M(q0(M(a), b)))` otherwise (`M_veblen_of_notMem`), where
  `q0(c, b)` is the least `q` with `b < φ(c, q)`.

The last case is why the induction carries `q0`: `MQ T x` says that the principal summands of
`x` and of every `q0(c, x)` are in `T` together with their `M`.
-/

namespace Googology.Notation.InaccPsi

open Ordinal Set

universe u

namespace InaccSeq

variable {S : InaccSeq.{u}}

variable (S) in
/-- `M e g x`: the least member of `Cl(e, g)` at or above `x`. -/
noncomputable def M (e g x : Ordinal.{u}) : Ordinal.{u} := sInf (S.CSet e g ∩ Ici x)

variable {e g : Ordinal.{u}}

theorem M_spec {x : Ordinal.{u}} (hx : x < S.Lam) :
    S.M e g x ∈ S.CSet e g ∧ x ≤ S.M e g x := by
  obtain ⟨z, hz, hxz⟩ := exists_mem_ge (S := S) hx e g
  exact csInf_mem (⟨z, hz, hxz⟩ : (S.CSet e g ∩ Ici x).Nonempty)

theorem M_le {x z : Ordinal.{u}} (hz : z ∈ S.CSet e g) (hxz : x ≤ z) : S.M e g x ≤ z :=
  csInf_le' ⟨hz, hxz⟩

theorem M_eq_self {x : Ordinal.{u}} (hx : x ∈ S.CSet e g) : S.M e g x = x :=
  le_antisymm (M_le hx le_rfl)
    (csInf_mem (⟨x, hx, Set.self_mem_Ici⟩ : (S.CSet e g ∩ Ici x).Nonempty)).2

theorem M_mono {x y : Ordinal.{u}} (h : x ≤ y) (hy : y < S.Lam) : S.M e g x ≤ S.M e g y :=
  M_le (M_spec hy).1 (h.trans (M_spec hy).2)

theorem lt_of_mem_lt_M {x w : Ordinal.{u}} (hw : w ∈ S.CSet e g) (h : w < S.M e g x) : w < x :=
  not_le.1 fun h' => absurd (M_le hw h') (not_le.2 h)

theorem le_of_notMem {x : Ordinal.{u}} (hx : x ∉ S.CSet e g) : g ≤ x :=
  not_lt.1 fun h => hx (CSet.of_lt h)

theorem lt_M_of_notMem {x : Ordinal.{u}} (hx : x < S.Lam) (hR : x ∉ S.CSet e g) :
    x < S.M e g x :=
  lt_of_le_of_ne (M_spec hx).2 fun h => hR (h ▸ (M_spec hx).1)

/-! ## Principal summands -/

/-- Above a principal `x` outside `R`, the next member of `R` is principal. -/
theorem M_principal {x : Ordinal.{u}} (hx : x < S.Lam) (hP : IsPrincipal (· + ·) x)
    (hx0 : x ≠ 0) : IsPrincipal (· + ·) (S.M e g x) ∧ S.M e g x ≠ 0 := by
  obtain ⟨hmR, hxm⟩ := M_spec (e := e) (g := g) hx
  have hm0 : S.M e g x ≠ 0 := fun h => hx0 (le_antisymm (h ▸ hxm) zero_le)
  obtain ⟨h, rfl⟩ := exists_opow_of_principal hP hx0
  have hl : ω ^ h ≤ lead (S.M e g (ω ^ h)) := opow_le_lead hxm
  have heq : lead (S.M e g (ω ^ h)) = S.M e g (ω ^ h) :=
    le_antisymm (lead_le hm0) (M_le (lead_tail_mem hmR hm0).1 hl)
  refine ⟨?_, hm0⟩
  rw [← heq]; exact isPrincipal_add_omega0_opow _

/-- Above a principal `x` outside `R`, the next member of `R` is strongly critical or a
Veblen value of members of `R` below `x`. -/
theorem M_cases {x : Ordinal.{u}} (hx : x < S.Lam) (hP : IsPrincipal (· + ·) x) (hx0 : x ≠ 0)
    (hR : x ∉ S.CSet e g) :
    SC (S.M e g x) ∨ ∃ p q, p ∈ S.CSet e g ∧ q ∈ S.CSet e g ∧ p < x ∧ q < x ∧
      S.M e g x = veblen p q := by
  obtain ⟨hzR, _⟩ := M_spec (e := e) (g := g) hx
  have hxlt := lt_M_of_notMem hx hR
  obtain ⟨hPz, hz0⟩ := M_principal (e := e) (g := g) hx hP hx0
  rcases prin_mem_cases hzR ((le_of_notMem hR).trans hxlt.le) hPz hz0 with
    ⟨m, hm⟩ | hw | ⟨p, q, hpR, hqR, hp, hq, hpq⟩ | ⟨p, _, _, hpz⟩ | ⟨π, y', hπ, _, _, _, hz'⟩
  · left; rw [hm]; exact SC_I m
  · left; rw [hw]; exact SC_Iw
  · right; exact ⟨p, q, hpR, hqR, lt_of_mem_lt_M hpR hp, lt_of_mem_lt_M hqR hq, hpq⟩
  · left
    have hp0 : p ≠ 0 := fun h => hz0 (by rw [hpz, h, Om_zero])
    rw [hpz]; exact SC_Om hp0
  · left; rw [hz']; exact SC_psi hπ y'

/-- **`M(Ω_a) = Ω_{M(a)}`.** -/
theorem M_Om {a : Ordinal.{u}} (ha : a < S.Lam) : S.M e g (Om a) = Om (S.M e g a) := by
  have hOa : Om a < S.Lam := Om_lt_Lam ha
  obtain ⟨hzR, hxz⟩ := M_spec (e := e) (g := g) hOa
  obtain ⟨hmR, ham⟩ := M_spec (e := e) (g := g) ha
  refine le_antisymm (M_le (CSet.Om_mem hmR) (Om_le_Om.2 ham)) ?_
  obtain ⟨σ, h1, h2⟩ := exists_Om_between (S.M e g (Om a))
  have hσR : σ ∈ S.CSet e g := mem_of_Om_mem (Om_mem_of_between hzR h1 h2)
  have haσ : a ≤ σ := le_of_Om_lt_Om_succ (lt_of_le_of_lt hxz h2)
  exact le_trans (Om_le_Om.2 (M_le hσR haσ)) h1

/-- The last step of the collapse cases: if `R` has `ψ_κ(y')` above `ψ_κ(y)`, then
`M(ψ_κ(y)) = ψ_κ(M(y))`. -/
theorem M_psi_of_mem {κ y y' : Ordinal.{u}} (hκ : S.InR κ) (hκR : κ ∈ S.CSet e g)
    (hy : y < S.Lam) (hy'R : y' ∈ S.CSet e g) (hy'e : y' < e)
    (hlt : S.psi y κ < S.M e g (S.psi y κ)) (hz : S.M e g (S.psi y κ) = S.psi y' κ) :
    S.M e g y < e ∧ S.M e g (S.psi y κ) = S.psi (S.M e g y) κ := by
  have hyy' : y < y' := by
    by_contra h
    have := (psi_mono hκ (not_lt.1 h)).1
    rw [← hz] at this
    exact absurd hlt (not_lt.2 this)
  have hMy : S.M e g y ≤ y' := M_le hy'R hyy'.le
  have hMye : S.M e g y < e := lt_of_le_of_lt hMy hy'e
  obtain ⟨hMyR, hyMy⟩ := M_spec (e := e) (g := g) hy
  have hXR : S.psi (S.M e g y) κ ∈ S.CSet e g := CSet.psi_mem hMye hκ hκR hMyR
  refine ⟨hMye, le_antisymm (M_le hXR (psi_mono hκ hyMy).1) ?_⟩
  rw [hz]; exact (psi_mono hκ hMy).1

/-- **`M(ψ_{I_n}(y))` is `I_n` or `ψ_{I_n}(M(y))`.** -/
theorem M_psiI {y : Ordinal.{u}} {n : ℕ} (hy : y < S.Lam)
    (hR : S.psi y (S.I n) ∉ S.CSet e g) :
    S.M e g (S.psi y (S.I n)) = S.I n ∨
      (S.M e g y < e ∧ S.M e g (S.psi y (S.I n)) = S.psi (S.M e g y) (S.I n)) := by
  have hxI : S.psi y (S.I n) < S.I n := psi_lt (InR_I n) y
  have hxL : S.psi y (S.I n) < S.Lam := hxI.trans (I_lt_Lam n)
  obtain ⟨hzR, _⟩ := M_spec (e := e) (g := g) hxL
  have hxlt := lt_M_of_notMem hxL hR
  by_cases hIz : S.I n ≤ S.M e g (S.psi y (S.I n))
  · exact Or.inl (le_antisymm (M_le (CSet.I_mem e g n) hxI.le) hIz)
  right
  have hzI := not_le.1 hIz
  obtain ⟨σ, h1, h2⟩ := exists_Om_between (S.M e g (S.psi y (S.I n)))
  have hσR : σ ∈ S.CSet e g := mem_of_Om_mem (Om_mem_of_between hzR h1 h2)
  have hfx : Om (S.psi y (S.I n)) = S.psi y (S.I n) := Om_psiI y n
  have hxσ : S.psi y (S.I n) ≤ σ :=
    le_of_Om_lt_Om_succ (by rw [hfx]; exact lt_trans hxlt h2)
  have hzσ := M_le hσR hxσ
  have hzeq : S.M e g (S.psi y (S.I n)) = σ := le_antisymm hzσ ((le_Om σ).trans h1)
  have hfz : Om (S.M e g (S.psi y (S.I n))) = S.M e g (S.psi y (S.I n)) := by
    have h1' := h1
    rw [← hzeq] at h1'
    exact le_antisymm h1' (le_Om _)
  have hz0 : S.M e g (S.psi y (S.I n)) ≠ 0 :=
    (lt_of_le_of_lt zero_le hxlt).ne'
  have hSC : SC (S.M e g (S.psi y (S.I n))) := by rw [← hfz]; exact SC_Om hz0
  rcases prin_mem_cases hzR ((le_of_notMem hR).trans hxlt.le) hSC.isPrincipal hz0 with
    ⟨m, hm⟩ | hw | ⟨p, q, _, _, hp, hq, hpq⟩ | ⟨p, _, hp, hpz⟩ |
      ⟨π, y', hπ, hπR, hy'R, hy'e, hz'⟩
  · exfalso
    have hmn : m < n := S.strictMono.lt_iff_lt.1 (hm ▸ hzI)
    have := I_lt_psiI_of_lt (S := S) y hmn
    rw [← hm] at this
    exact lt_irrefl _ (this.trans hxlt)
  · exfalso
    rw [hw] at hzI
    exact lt_asymm hzI (S.I_lt_Iw n)
  · exact absurd hpq.symm (hSC.not_veblen_lt hp hq)
  · exfalso
    have : S.M e g (S.psi y (S.I n)) = p := Om_inj.1 (hfz.trans hpz)
    rw [this] at hp; exact lt_irrefl _ hp
  · rcases hπ with ⟨m, rfl⟩ | ⟨s', rfl⟩
    · rcases lt_trichotomy m n with hmn | rfl | hmn
      · exfalso
        have h3 := lt_trans (psi_lt (S := S) (InR_I m) y') (I_lt_psiI_of_lt y hmn)
        rw [← hz'] at h3
        exact lt_asymm h3 hxlt
      · exact M_psi_of_mem (InR_I m) hπR hy hy'R hy'e hxlt hz'
      · exfalso
        have h3 := I_lt_psiI_of_lt (S := S) y' hmn
        rw [← hz'] at h3
        exact lt_asymm h3 hzI
    · exfalso
      have hb := psiS_bounds (S := S) y' s'
      rw [← hz'] at hb
      exact not_Om_of_between hb.1 hb.2 _ hfz.symm

/-- **`M(ψ_{Ω_{s+1}}(y))` is `Ω_{s+1}`, `Ω_{M(s)}` or `ψ_{Ω_{s+1}}(M(y))`.** -/
theorem M_psiS {y s : Ordinal.{u}} (hy : y < S.Lam) (hs : s < S.Lam)
    (hR : S.psi y (Om (s + 1)) ∉ S.CSet e g) :
    S.M e g (S.psi y (Om (s + 1))) = Om (s + 1) ∨
      S.M e g (S.psi y (Om (s + 1))) = Om (S.M e g s) ∨
      (S.M e g y < e ∧ S.M e g (S.psi y (Om (s + 1))) = S.psi (S.M e g y) (Om (s + 1))) := by
  have hb := psiS_bounds (S := S) y s
  have hs1L : Om (s + 1) < S.Lam := Om_lt_Lam (add_one_lt_Lam hs)
  have hxL : S.psi y (Om (s + 1)) < S.Lam := hb.2.trans hs1L
  obtain ⟨hzR, _⟩ := M_spec (e := e) (g := g) hxL
  have hxlt := lt_M_of_notMem hxL hR
  by_cases hz1 : S.M e g (S.psi y (Om (s + 1))) < Om (s + 1)
  · right; right
    have hSCx : SC (S.psi y (Om (s + 1))) := SC_psi (InR_Om_succ s) y
    obtain ⟨hPz, hz0⟩ := M_principal (e := e) (g := g) hxL hSCx.isPrincipal hSCx.1.ne'
    have h1 : Om s < S.M e g (S.psi y (Om (s + 1))) := hb.1.trans hxlt
    rcases prin_mem_cases hzR ((le_of_notMem hR).trans hxlt.le) hPz hz0 with
      ⟨m, hm⟩ | hw | ⟨p, q, hpR, hqR, hp, hq, hpq⟩ | ⟨p, _, _, hpz⟩ |
        ⟨π, y', hπ, hπR, hy'R, hy'e, hz'⟩
    · exact absurd (hm.trans (Om_I m).symm) (not_Om_of_between h1 hz1 _)
    · exact absurd (hw.trans S.Om_Iw.symm) (not_Om_of_between h1 hz1 _)
    · exfalso
      have := hSCx.2 p (lt_of_mem_lt_M hpR hp) q (lt_of_mem_lt_M hqR hq)
      rw [← hpq] at this
      exact lt_asymm this hxlt
    · exact absurd hpz (not_Om_of_between h1 hz1 _)
    · rcases hπ with ⟨m, rfl⟩ | ⟨s', rfl⟩
      · exfalso
        have : S.M e g (S.psi y (Om (s + 1))) = Om (S.M e g (S.psi y (Om (s + 1)))) := by
          rw [hz', Om_psiI]
        exact not_Om_of_between h1 hz1 _ this
      · have hss : s' = s := by
          have hb' := psiS_bounds (S := S) y' s'
          rw [← hz'] at hb'
          exact between_unique hb'.1 hb'.2 h1 hz1
        subst hss
        exact M_psi_of_mem (InR_Om_succ s') hπR hy hy'R hy'e hxlt hz'
  · by_cases hR1 : Om (s + 1) ∈ S.CSet e g
    · left; exact le_antisymm (M_le hR1 hb.2.le) (not_lt.1 hz1)
    · right; left
      have hzM : S.M e g (S.psi y (Om (s + 1))) = S.M e g (Om (s + 1)) :=
        le_antisymm (M_mono hb.2.le hs1L) (M_le hzR (not_lt.1 hz1))
      rw [hzM, M_Om (add_one_lt_Lam hs)]
      congr 1
      have hs1R : s + 1 ∉ S.CSet e g := fun h => hR1 (CSet.Om_mem h)
      have hsR : s ∉ S.CSet e g := fun h => hs1R (CSet.succ_mem h)
      have hslt := lt_M_of_notMem hs hsR
      exact le_antisymm (M_le (M_spec hs).1 (Order.add_one_le_of_lt hslt))
        (M_mono le_self_add (add_one_lt_Lam hs))

/-- **`M(φ(a, b)) = φ(a, M(b))`** for `a ∈ R`. -/
theorem M_veblen_of_mem {a b : Ordinal.{u}} (hx : veblen a b < S.Lam)
    (hR : veblen a b ∉ S.CSet e g) (hb : b < veblen a b) (haR : a ∈ S.CSet e g) :
    S.M e g (veblen a b) = veblen a (S.M e g b) := by
  have hbL : b < S.Lam := hb.trans hx
  obtain ⟨hMbR, hbMb⟩ := M_spec (e := e) (g := g) hbL
  obtain ⟨hzR, _⟩ := M_spec (e := e) (g := g) hx
  have hxlt := lt_M_of_notMem hx hR
  have ha : a < veblen a b := lt_of_le_of_ne (left_le_veblen a b) fun h => hR (h ▸ haR)
  refine le_antisymm (M_le (CSet.phi_mem haR hMbR) (veblen_le_veblen_iff_right.2 hbMb)) ?_
  have hbz : b < S.M e g (veblen a b) := hb.trans hxlt
  have hMbz : S.M e g b ≤ S.M e g (veblen a b) := M_le hzR hbz.le
  rcases M_cases hx (veblen_isPrincipal a b) veblen_pos.ne' hR with
    hSC | ⟨p, q, _, hqR, _, hqx, hpq⟩
  · calc veblen a (S.M e g b) ≤ veblen a (S.M e g (veblen a b)) :=
          veblen_le_veblen_iff_right.2 hMbz
      _ = S.M e g (veblen a b) := hSC.veblen_right (ha.trans hxlt)
  · rcases lt_trichotomy p a with hpa | rfl | hpa
    · exfalso
      have h1 : veblen p (veblen a b) < veblen p q := by
        rw [veblen_veblen_of_lt hpa, ← hpq]; exact hxlt
      exact absurd (veblen_lt_veblen_iff_right.1 h1) (not_lt.2 hqx.le)
    · have hbq : b < q := veblen_lt_veblen_iff_right.1 (by rw [← hpq]; exact hxlt)
      rw [hpq]; exact veblen_le_veblen_iff_right.2 (M_le hqR hbq.le)
    · have hfix : veblen a (S.M e g (veblen a b)) = S.M e g (veblen a b) := by
        rw [hpq]; exact veblen_veblen_of_lt hpa q
      calc veblen a (S.M e g b) ≤ veblen a (S.M e g (veblen a b)) :=
            veblen_le_veblen_iff_right.2 hMbz
        _ = S.M e g (veblen a b) := hfix

/-- **`M(φ(a, b)) = φ(M(a), M(q0(M(a), b)))`** for `a ∉ R`. -/
theorem M_veblen_of_notMem {a b : Ordinal.{u}} (hx : veblen a b < S.Lam)
    (hR : veblen a b ∉ S.CSet e g) (ha : a < veblen a b) (hb : b < veblen a b)
    (haR : a ∉ S.CSet e g) :
    S.M e g (veblen a b) = veblen (S.M e g a) (S.M e g (q0 (S.M e g a) b)) := by
  have haL : a < S.Lam := ha.trans hx
  have hbL : b < S.Lam := hb.trans hx
  obtain ⟨hcR, _⟩ := M_spec (e := e) (g := g) haL
  have hac : a < S.M e g a := lt_M_of_notMem haL haR
  have hqL : q0 (S.M e g a) b < S.Lam :=
    lt_of_le_of_lt (q0_le_add_one _ b) (add_one_lt_Lam hbL)
  obtain ⟨hwR, hqw⟩ := M_spec (e := e) (g := g) hqL
  obtain ⟨hzR, _⟩ := M_spec (e := e) (g := g) hx
  have hxlt := lt_M_of_notMem hx hR
  generalize hc : S.M e g a = c at hcR hac hqL hwR hqw ⊢
  generalize hw : S.M e g (q0 c b) = w at hwR hqw ⊢
  have hbcw : b < veblen c w :=
    lt_of_lt_of_le (lt_veblen_q0 c b) (veblen_le_veblen_iff_right.2 hqw)
  have hge : veblen a b ≤ veblen c w := by
    rw [← veblen_veblen_of_lt hac w]; exact veblen_le_veblen_iff_right.2 hbcw.le
  refine le_antisymm (M_le (CSet.phi_mem hcR hwR) hge) ?_
  generalize hz : S.M e g (veblen a b) = z at hzR hxlt ⊢
  have hbz : b < z := hb.trans hxlt
  have haz : a < z := ha.trans hxlt
  have hcz : c ≤ z := by rw [← hc]; exact M_le hzR haz.le
  have key : veblen c z = z → veblen c w ≤ z := fun hfix => by
    have : q0 c b ≤ z := q0_le (by rw [hfix]; exact hbz)
    calc veblen c w ≤ veblen c z := by
          rw [← hw]; exact veblen_le_veblen_iff_right.2 (M_le hzR this)
      _ = z := hfix
  rcases M_cases (e := e) (g := g) hx (veblen_isPrincipal a b) veblen_pos.ne' hR with
    hSC | ⟨p, q, hpR, hqR, _, hqx, hpq⟩
  · rw [hz] at hSC
    rcases hcz.lt_or_eq with hlt | heq
    · exact key (hSC.veblen_right hlt)
    · have hq00 : q0 c b = 0 := q0_of_lt (by rw [heq, hSC.veblen_zero]; exact hbz)
      have hw0 : w = 0 := by rw [← hw, hq00]; exact M_eq_self (CSet.zero_mem e g)
      exact (show veblen c w = z by rw [hw0, heq, hSC.veblen_zero]).le
  · rw [hz] at hpq
    rcases lt_trichotomy p a with hpa | rfl | hpa
    · exfalso
      have h1 : veblen p (veblen a b) < veblen p q := by
        rw [veblen_veblen_of_lt hpa, ← hpq]; exact hxlt
      exact absurd (veblen_lt_veblen_iff_right.1 h1) (not_lt.2 hqx.le)
    · exact absurd hpR haR
    · have hcp : c ≤ p := by rw [← hc]; exact M_le hpR hpa.le
      rcases hcp.lt_or_eq with hcp' | heq
      · exact key (by rw [hpq]; exact veblen_veblen_of_lt hcp' q)
      · have hbq : q0 c b ≤ q := q0_le (by rw [heq, ← hpq]; exact hbz)
        rw [hpq, ← heq, ← hw]; exact veblen_le_veblen_iff_right.2 (M_le hqR hbq)

/-! ## Target sets -/

/-- The closure conditions on a target set `T`: closed under the operations of `Cl`, with
collapses at arguments below `e`, and below `Λ`. -/
structure Closed (S : InaccSeq.{u}) (e : Ordinal.{u}) (T : Set Ordinal.{u}) : Prop where
  zero : (0 : Ordinal.{u}) ∈ T
  I : ∀ n, S.I n ∈ T
  add : ∀ x y, x ∈ T → y ∈ T → x + y ∈ T
  phi : ∀ x y, x ∈ T → y ∈ T → veblen x y ∈ T
  om : ∀ x, x ∈ T → Om x ∈ T
  psiS : ∀ s w, s ∈ T → w ∈ T → w < e → S.psi w (Om (s + 1)) ∈ T
  psiI : ∀ n w, w ∈ T → w < e → S.psi w (S.I n) ∈ T
  lt : ∀ x ∈ T, x < S.Lam

variable (S e g) in
/-- The principal summands of `x` are in `T`, and so is `M` of each. -/
def MGood (T : Set Ordinal.{u}) (x : Ordinal.{u}) : Prop :=
  ∀ h, Comp h x → (ω : Ordinal.{u}) ^ h ∈ T ∧ S.M e g (ω ^ h) ∈ T

variable (S e g) in
/-- `x` and every `q0(c, x)` are `MGood`. -/
def MQ (T : Set Ordinal.{u}) (x : Ordinal.{u}) : Prop :=
  MGood S e g T x ∧ ∀ c, MGood S e g T (q0 c x)

variable {T : Set Ordinal.{u}}

theorem Closed.one_mem (hT : Closed S e T) : (1 : Ordinal.{u}) ∈ T := by
  have := hT.phi 0 0 hT.zero hT.zero
  rwa [veblen_zero_apply, opow_zero] at this

theorem MGood_zero : MGood S e g T 0 := fun h hc => absurd hc (not_comp_zero h)

theorem MGood_add {a b : Ordinal.{u}} (ha : MGood S e g T a) (hb : MGood S e g T b) :
    MGood S e g T (a + b) := fun h hc => (Comp.add hc).elim (ha h) (hb h)

theorem MGood_one (hT : Closed S e T) : MGood S e g T 1 := by
  intro h hc
  rw [show (1 : Ordinal.{u}) = ω ^ (0 : Ordinal.{u}) from (opow_zero ω).symm] at hc
  rw [hc.eq_of_opow, opow_zero, M_eq_self (CSet.one_mem e g)]
  exact ⟨hT.one_mem, hT.one_mem⟩

theorem MGood_succ (hT : Closed S e T) {a : Ordinal.{u}} (ha : MGood S e g T a) :
    MGood S e g T (a + 1) := MGood_add ha (MGood_one hT)

theorem MGood_prin {x : Ordinal.{u}} (hP : IsPrincipal (· + ·) x) (hx0 : x ≠ 0) (hxT : x ∈ T)
    (hMT : S.M e g x ∈ T) : MGood S e g T x := fun h hc => by
  rw [Comp.eq_of_principal hP hx0 hc]; exact ⟨hxT, hMT⟩

theorem MGood_small {x : Ordinal.{u}} (hxg : x < g) (hall : ∀ z ≤ x, z ∈ T) :
    MGood S e g T x := fun h hc => by
  have hle := hc.opow_le
  rw [M_eq_self (CSet.of_lt (lt_of_le_of_lt hle hxg))]
  exact ⟨hall _ hle, hall _ hle⟩

theorem mem_of_Good (hT : Closed S e T) {x : Ordinal.{u}} (hx : MGood S e g T x) : x ∈ T :=
  mem_of_comps hT.zero hT.add x fun h hc => (hx h hc).1

theorem opow_add_one_le_of_notMem {h z : Ordinal.{u}} (hp : (ω : Ordinal.{u}) ^ h ∉ S.CSet e g)
    (hz : z ∈ S.CSet e g) (hle : ω ^ h ≤ z) : ω ^ (h + 1) ≤ z := by
  have hz0 : z ≠ 0 := ne_of_gt (lt_of_lt_of_le (Ordinal.opow_pos h omega0_pos) hle)
  have hlog : h ≤ Ordinal.log ω z := Ordinal.le_log_of_opow_le Ordinal.one_lt_omega0 hle
  rcases eq_or_lt_of_le hlog with h' | h'
  · exact absurd (h' ▸ (lead_tail_mem hz hz0).1) hp
  · exact le_trans (Ordinal.opow_le_opow_right omega0_pos (Order.add_one_le_of_lt h'))
      (lead_le hz0)

/-- **`M(x) ∈ T` when `x` is `MGood`.** The leading summand `p` stays when it is in `R`, and
then `M(x) = p + M(rest)`; otherwise `M(x) = M(p)`. -/
theorem M_mem_of_Good (hT : Closed S e T) :
    ∀ x : Ordinal.{u}, x < S.Lam → MGood S e g T x → S.M e g x ∈ T := by
  intro x
  induction x using WellFoundedLT.induction with
  | _ x IH =>
    intro hx hcomp
    by_cases hx0 : x = 0
    · subst hx0
      rw [M_eq_self (CSet.zero_mem e g)]
      exact hT.zero
    set h := Ordinal.log ω x with hh
    have hpS := hcomp h (comp_lead hx0)
    have hr : tail x < x := tail_lt hx0
    have hMr : S.M e g (tail x) ∈ T :=
      IH _ hr (lt_trans hr hx) (fun h' hc => hcomp h' (Comp.of_tail hx0 hc))
    obtain ⟨hMxR, hxMx⟩ := M_spec (e := e) (g := g) hx
    by_cases hpR : (ω : Ordinal.{u}) ^ h ∈ S.CSet e g
    · obtain ⟨hMrR, hrMr⟩ := M_spec (e := e) (g := g) (lt_trans hr hx)
      have hsum : S.M e g x = ω ^ h + S.M e g (tail x) := by
        refine le_antisymm (M_le (CSet.add_mem hpR hMrR) ?_) ?_
        · conv_lhs => rw [← lead_add_tail hx0]
          exact (add_le_add_iff_left _).2 hrMr
        · have hpm : (ω : Ordinal.{u}) ^ h ≤ S.M e g x := le_trans (lead_le hx0) hxMx
          have hm0 : S.M e g x ≠ 0 :=
            ne_of_gt (lt_of_lt_of_le (Ordinal.opow_pos _ omega0_pos) hpm)
          have hlog : h ≤ Ordinal.log ω (S.M e g x) :=
            Ordinal.le_log_of_opow_le Ordinal.one_lt_omega0 hpm
          rcases eq_or_lt_of_le hlog with hl | hl
          · have hlead : lead (S.M e g x) = ω ^ h := by rw [lead, ← hl]
            have htR := (lead_tail_mem hMxR hm0).2
            have hdec := lead_add_tail hm0
            rw [hlead] at hdec
            have hrt : tail x ≤ tail (S.M e g x) := by
              have h1 : ω ^ h + tail x ≤ ω ^ h + tail (S.M e g x) := by
                rw [hdec]
                conv_lhs => rw [show (ω : Ordinal.{u}) ^ h = lead x from rfl, lead_add_tail hx0]
                exact hxMx
              exact (add_le_add_iff_left _).1 h1
            conv_rhs => rw [← hdec]
            exact (add_le_add_iff_left _).2 (M_le htR hrt)
          · have hbig : (ω : Ordinal.{u}) ^ (h + 1) ≤ S.M e g x :=
              le_trans (Ordinal.opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hl))
                (lead_le hm0)
            refine le_trans (le_of_lt ?_) hbig
            have hne : h + 1 ≠ 0 := (add_pos_of_right zero_lt_one h).ne'
            obtain ⟨e', he', n, hn⟩ := (Ordinal.lt_omega0_opow hne).1 (tail_lt_opow x)
            have hle : (ω : Ordinal.{u}) ^ e' * n ≤ ω ^ h * n :=
              mul_le_mul_left
                (Ordinal.opow_le_opow_right omega0_pos (Order.lt_add_one_iff.1 he')) _
            have hMrle : S.M e g (tail x) ≤ ω ^ h * n :=
              M_le (mul_nat_mem hpR n) (le_of_lt (lt_of_lt_of_le hn hle))
            refine Ordinal.isPrincipal_add_omega0_opow (h + 1) (opow_lt_opow_add_one h) ?_
            exact lt_of_le_of_lt hMrle (Ordinal.omega0_opow_mul_nat_lt (lt_add_one h) n)
      rw [hsum]
      exact hT.add _ _ hpS.1 hMr
    · obtain ⟨hMpR, hpMp⟩ := M_spec (e := e) (g := g)
        (lt_of_le_of_lt (lead_le hx0) hx : (ω : Ordinal.{u}) ^ h < S.Lam)
      have heq : S.M e g x = S.M e g (ω ^ h) := by
        refine le_antisymm (M_le hMpR ?_) (M_le hMxR (le_trans (lead_le hx0) hxMx))
        exact le_trans (le_of_lt (lt_opow_log_add_one x))
          (opow_add_one_le_of_notMem hpR hMpR hpMp)
      rw [heq]
      exact hpS.2

/-! ## The one-step lemmas for `MQ` -/

theorem MQ_zero : MQ S e g T 0 :=
  ⟨MGood_zero, fun c => by rw [q0_zero]; exact MGood_zero⟩

theorem MQ_add {a b : Ordinal.{u}} (ha : MQ S e g T a) (hb : MQ S e g T b) :
    MQ S e g T (a + b) := by
  refine ⟨MGood_add ha.1 hb.1, fun c => ?_⟩
  rw [q0_add]
  rcases max_choice (q0 c a) (q0 c b) with h | h <;> rw [h]
  · exact ha.2 c
  · exact hb.2 c

theorem MQ_SC (hT : Closed S e T) {x : Ordinal.{u}} (hSC : SC x) (hxT : x ∈ T)
    (hMT : S.M e g x ∈ T) : MQ S e g T x := by
  have G : MGood S e g T x := MGood_prin hSC.isPrincipal hSC.1.ne' hxT hMT
  refine ⟨G, fun c => ?_⟩
  rcases q0_SC hSC c with h | h | h <;> rw [h]
  · exact MGood_zero
  · exact MGood_one hT
  · exact MGood_succ hT G

theorem MQ_mem (hT : Closed S e T) {x : Ordinal.{u}} (hSC : SC x) (hxR : x ∈ S.CSet e g)
    (hxT : x ∈ T) : MQ S e g T x :=
  MQ_SC hT hSC hxT (by rw [M_eq_self hxR]; exact hxT)

theorem MQ_small (hT : Closed S e T) {x : Ordinal.{u}} (hxg : x < g)
    (hall : ∀ z ≤ x, z ∈ T) : MQ S e g T x := by
  have G : MGood S e g T x := MGood_small hxg hall
  refine ⟨G, fun c => ?_⟩
  rcases (q0_le_add_one c x).lt_or_eq with h | h
  · have h' := Order.lt_add_one_iff.1 h
    exact MGood_small (lt_of_le_of_lt h' hxg) fun z hz => hall z (hz.trans h')
  · rw [h]; exact MGood_succ hT G

theorem MQ_phi (hT : Closed S e T) {a b : Ordinal.{u}} (ha : MQ S e g T a)
    (hb : MQ S e g T b) : MQ S e g T (veblen a b) := by
  have haT := mem_of_Good hT ha.1
  have hbT := mem_of_Good hT hb.1
  have hxT := hT.phi a b haT hbT
  have hxL := hT.lt _ hxT
  by_cases hxa : veblen a b = a
  · rw [hxa]; exact ha
  by_cases hxb : veblen a b = b
  · rw [hxb]; exact hb
  have hal : a < veblen a b := lt_of_le_of_ne (left_le_veblen a b) (Ne.symm hxa)
  have hbl : b < veblen a b := lt_of_le_of_ne (right_le_veblen a b) (Ne.symm hxb)
  have hMT : S.M e g (veblen a b) ∈ T := by
    by_cases hR : veblen a b ∈ S.CSet e g
    · rw [M_eq_self hR]; exact hxT
    by_cases haR : a ∈ S.CSet e g
    · rw [M_veblen_of_mem hxL hR hbl haR]
      exact hT.phi _ _ haT (M_mem_of_Good hT b (hT.lt _ hbT) hb.1)
    · rw [M_veblen_of_notMem hxL hR hal hbl haR]
      have hMa := M_mem_of_Good hT a (hT.lt _ haT) ha.1
      exact hT.phi _ _ hMa (M_mem_of_Good hT _
        (lt_of_le_of_lt (q0_le_add_one _ _) (add_one_lt_Lam (hT.lt _ hbT))) (hb.2 _))
  have G : MGood S e g T (veblen a b) :=
    MGood_prin (veblen_isPrincipal a b) veblen_pos.ne' hxT hMT
  refine ⟨G, fun c => ?_⟩
  rcases q0_veblen c a b with h | h | h <;> rw [h]
  · exact hb.2 c
  · exact MGood_succ hT hb.1
  · exact MGood_succ hT G

theorem MQ_Om (hT : Closed S e T) {a : Ordinal.{u}} (ha : MQ S e g T a) :
    MQ S e g T (Om a) := by
  by_cases ha0 : a = 0
  · rw [ha0, Om_zero]; exact MQ_zero
  have haT := mem_of_Good hT ha.1
  have haL := hT.lt _ haT
  refine MQ_SC hT (SC_Om ha0) (hT.om _ haT) ?_
  rw [M_Om haL]
  exact hT.om _ (M_mem_of_Good hT a haL ha.1)

theorem MQ_psiS (hT : Closed S e T) {s y : Ordinal.{u}} (hs : MGood S e g T s)
    (hy : MGood S e g T y) (hxT : S.psi y (Om (s + 1)) ∈ T) :
    MQ S e g T (S.psi y (Om (s + 1))) := by
  have hsT := mem_of_Good hT hs
  have hyT := mem_of_Good hT hy
  have hsL := hT.lt _ hsT
  have hyL := hT.lt _ hyT
  refine MQ_SC hT (SC_psi (InR_Om_succ s) y) hxT ?_
  by_cases hR : S.psi y (Om (s + 1)) ∈ S.CSet e g
  · rw [M_eq_self hR]; exact hxT
  rcases M_psiS hyL hsL hR with h | h | ⟨hlt, h⟩ <;> rw [h]
  · exact hT.om _ (hT.add _ _ hsT hT.one_mem)
  · exact hT.om _ (M_mem_of_Good hT s hsL hs)
  · exact hT.psiS s _ hsT (M_mem_of_Good hT y hyL hy) hlt

theorem MQ_psiI (hT : Closed S e T) {n : ℕ} {y : Ordinal.{u}} (hy : MGood S e g T y)
    (hxT : S.psi y (S.I n) ∈ T) : MQ S e g T (S.psi y (S.I n)) := by
  have hyT := mem_of_Good hT hy
  have hyL := hT.lt _ hyT
  refine MQ_SC hT (SC_psi (InR_I n) y) hxT ?_
  by_cases hR : S.psi y (S.I n) ∈ S.CSet e g
  · rw [M_eq_self hR]; exact hxT
  rcases M_psiI hyL hR with h | ⟨hlt, h⟩ <;> rw [h]
  · exact hT.I n
  · exact hT.psiI n _ (M_mem_of_Good hT y hyL hy) hlt

/-! ## `M` does not leave `Cl(α, β)` -/

theorem closed_CSet {α β : Ordinal.{u}} (heα : e ≤ α) (hβL : β ≤ S.Lam) :
    Closed S e (S.CSet α β) where
  zero := CSet.zero_mem α β
  I := CSet.I_mem α β
  add := fun _ _ => CSet.add_mem
  phi := fun _ _ => CSet.phi_mem
  om := fun _ => CSet.Om_mem
  psiS := fun s _ hs hw hwe => CSet.psi_mem (lt_of_lt_of_le hwe heα) (InR_Om_succ s)
    (CSet.Om_mem (CSet.succ_mem hs)) hw
  psiI := fun n _ hw hwe => CSet.psi_mem (lt_of_lt_of_le hwe heα) (InR_I n) (CSet.I_mem α β n) hw
  lt := fun _ hx => lt_Lam_of_mem hβL hx

/-- **Every member of `Cl(α, β)` satisfies `MQ`**, for `R = Cl(e, g)` with `e ≤ α` and
`β ≤ g`. The second half is carried for the subscripts `Ω_{s+1}` of collapses. -/
theorem MQ_of_mem_CSet {α β x : Ordinal.{u}} (heα : e ≤ α) (hβg : β ≤ g) (hβL : β ≤ S.Lam)
    (hx : x ∈ S.CSet α β) :
    MQ S e g (S.CSet α β) x ∧ ∀ σ, x = Om σ → MGood S e g (S.CSet α β) σ := by
  have hT := closed_CSet (S := S) heα hβL
  have Om0 : ∀ σ : Ordinal.{u}, 0 = Om σ → σ = 0 := fun σ hσ => by
    by_contra h; exact (Om_pos h).ne' hσ.symm
  induction hx with
  | @small y h =>
    have hall : ∀ z ≤ y, z ∈ S.CSet α β := fun z hz => CSet.of_lt (lt_of_le_of_lt hz h)
    refine ⟨MQ_small hT (lt_of_lt_of_le h hβg) hall, fun σ hσ => ?_⟩
    have hσy : σ ≤ y := hσ ▸ le_Om σ
    exact MGood_small (lt_of_le_of_lt hσy (lt_of_lt_of_le h hβg))
      fun z hz => hall z (hz.trans hσy)
  | zero =>
    exact ⟨MQ_zero, fun σ hσ => by rw [Om0 σ hσ]; exact MGood_zero⟩
  | inacc n =>
    have Q := MQ_mem hT (SC_I n) (CSet.I_mem e g n) (CSet.I_mem α β n)
    refine ⟨Q, fun σ hσ => ?_⟩
    rw [← Om_inj.1 ((Om_I n).trans hσ)]; exact Q.1
  | inaccW =>
    have Q := MQ_mem hT SC_Iw (CSet.Iw_mem e g) (CSet.Iw_mem α β)
    refine ⟨Q, fun σ hσ => ?_⟩
    rw [← Om_inj.1 (S.Om_Iw.trans hσ)]; exact Q.1
  | @add p q _ _ ihp ihq =>
    refine ⟨MQ_add ihp.1 ihq.1, fun σ hσ => ?_⟩
    by_cases hσ0 : σ = 0
    · rw [hσ0]; exact MGood_zero
    by_cases hq0 : q = 0
    · rw [hq0, add_zero] at hσ; exact ihp.2 σ hσ
    have hpz : p < p + q := lt_add_of_pos_right p (pos_iff_ne_zero.2 hq0)
    have hP := (SC_Om hσ0).isPrincipal
    rw [hσ] at hpz
    have hqz : q = Om σ := le_antisymm (hσ ▸ le_add_self)
      (not_lt.1 fun h => absurd hσ (hP hpz h).ne)
    exact ihq.2 σ hqz
  | @phi p q _ _ ihp ihq =>
    refine ⟨MQ_phi hT ihp.1 ihq.1, fun σ hσ => ?_⟩
    by_cases hσ0 : σ = 0
    · rw [hσ0, Om_zero] at hσ; exact absurd hσ veblen_pos.ne'
    rcases (SC_Om hσ0).eq_of_veblen_eq hσ with h | h
    · exact ihp.2 σ h
    · exact ihq.2 σ h
  | @om p _ ihp =>
    refine ⟨MQ_Om hT ihp.1, fun σ hσ => ?_⟩
    rw [← Om_inj.1 hσ]; exact ihp.1.1
  | @coll π e' hπ hπC heC ihπ ihe =>
    rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
    · have Q := MQ_psiI hT ihe.1.1 (CSet.psi_mem e'.2 (InR_I n) hπC heC)
      refine ⟨Q, fun σ hσ => ?_⟩
      have : σ = S.psi e'.1 (S.I n) := Om_inj.1 (hσ.symm.trans (Om_psiI e'.1 n).symm)
      rw [this]; exact Q.1
    · have hs1 := ihπ.2 (s + 1) rfl
      have hs : MGood S e g (S.CSet α β) s := fun h hc => hs1 h hc.add_one
      have Q := MQ_psiS hT hs ihe.1.1 (CSet.psi_mem e'.2 (InR_Om_succ s) hπC heC)
      exact ⟨Q, fun σ hσ =>
        absurd hσ (not_Om_of_between (psiS_bounds _ _).1 (psiS_bounds _ _).2 σ)⟩

/-! ## The argument `M(e)` -/

/-- **Moving the argument up to `M(e)` does not change the closure.** -/
theorem CSet_M_subset : S.CSet (S.M e g e) g ⊆ S.CSet e g := by
  intro x hx
  induction hx with
  | small h => exact CSet.of_lt h
  | zero => exact CSet.zero_mem e g
  | inacc n => exact CSet.I_mem e g n
  | inaccW => exact CSet.Iw_mem e g
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy
  | om _ ih => exact CSet.Om_mem ih
  | @coll π y hπ _ _ ihπ ihy =>
    by_cases hye : y.1 < e
    · exact CSet.psi_mem hye hπ ihπ ihy
    · exact absurd (M_le ihy (not_lt.1 hye)) (not_le.2 y.2)

/-- **`ψ_κ(M(e)) = ψ_κ(e)`** for `M` relative to `Cl(e, ψ_κ(e))`. -/
theorem psi_M_eq {κ : Ordinal.{u}} (hκ : S.InR κ) (he : e < S.Lam) :
    S.psi (S.M e (S.psi e κ) e) κ = S.psi e κ := by
  have hem := (M_spec (e := e) (g := S.psi e κ) he).2
  refine le_antisymm (psi_le_of_good (CSet_mono hem le_rfl (mem_CSet_psi hκ e))
    fun x hx hxκ => lt_psi_of_mem hκ (CSet_M_subset hx) hxκ) (psi_mono hκ hem).1

/-- **`M(e)` lies in its own closure.** -/
theorem M_mem_self {κ : Ordinal.{u}} (hκ : S.InR κ) (he : e < S.Lam) :
    S.M e (S.psi e κ) e ∈ S.CSet (S.M e (S.psi e κ) e) (S.psi (S.M e (S.psi e κ) e) κ) := by
  obtain ⟨hmR, hem⟩ := M_spec (e := e) (g := S.psi e κ) he
  rw [psi_M_eq hκ he]
  exact CSet_mono hem le_rfl hmR

/-! ## Reading a collapse out of the closure -/

/-- **If `ψ_κ(d) ∈ Cl(α, β)` with `β ≤ ψ_κ(d)` and `d` in its own closure, then
`d ∈ Cl(α, β)` and `d < α`.** The closure made `ψ_κ(d)` as `ψ_κ(e)` with `e ∈ Cl(α, β)`,
`e < α`, and `d = M(e)`, which `MQ_of_mem_CSet` keeps inside. -/
theorem arg_mem_of_psi_mem {κ d α β : Ordinal.{u}} (hκ : S.InR κ)
    (hmem : S.psi d κ ∈ S.CSet α β) (hβz : β ≤ S.psi d κ) (hβL : β ≤ S.Lam)
    (hd : d ∈ S.CSet d (S.psi d κ)) : d ∈ S.CSet α β ∧ d < α := by
  have hdα : d < α := by
    by_contra hcon
    exact psi_notMem hκ d (CSet_mono (not_lt.1 hcon) hβz hmem)
  refine ⟨?_, hdα⟩
  have hSC := SC_psi hκ d
  rcases prin_mem_cases hmem hβz hSC.isPrincipal hSC.1.ne' with
    ⟨n, hn⟩ | hw | ⟨p, q, _, _, hp, hq, hpq⟩ | ⟨p, _, hp, hpz⟩ |
      ⟨π, e, hπ, _, heC, heα, hz⟩
  · exfalso
    rcases hκ with ⟨m, rfl⟩ | ⟨s, rfl⟩
    · have hnm : n < m := S.strictMono.lt_iff_lt.1 (hn ▸ psi_lt (InR_I m) d)
      have := I_lt_psiI_of_lt (S := S) d hnm
      rw [hn] at this; exact lt_irrefl _ this
    · exact not_Om_of_between (psiS_bounds d s).1 (psiS_bounds d s).2 (S.I n)
        (hn.trans (Om_I n).symm)
  · exfalso
    rcases hκ with ⟨m, rfl⟩ | ⟨s, rfl⟩
    · have := (psi_lt (S := S) (InR_I m) d).trans (S.I_lt_Iw m)
      rw [hw] at this; exact lt_irrefl _ this
    · exact not_Om_of_between (psiS_bounds d s).1 (psiS_bounds d s).2 S.Iw
        (hw.trans S.Om_Iw.symm)
  · exact absurd hpq.symm (hSC.not_veblen_lt hp hq)
  · exfalso
    rcases hκ with ⟨m, rfl⟩ | ⟨s, rfl⟩
    · have : S.psi d (S.I m) = p := Om_inj.1 ((Om_psiI d m).trans hpz)
      rw [this] at hp; exact lt_irrefl _ hp
    · exact not_Om_of_between (psiS_bounds d s).1 (psiS_bounds d s).2 p hpz
  · have hπκ : π = κ := sub_eq_of_psi_eq hπ hκ hz.symm
    subst hπκ
    have heL : e < S.Lam := lt_Lam_of_mem hβL heC
    have hg : S.psi e π = S.psi d π := hz.symm
    have hβg : β ≤ S.psi e π := hg ▸ hβz
    have hT := closed_CSet (S := S) (e := e) heα.le hβL
    have hQ := (MQ_of_mem_CSet (e := e) (g := S.psi e π) heα.le hβg hβL heC).1
    have hMmem : S.M e (S.psi e π) e ∈ S.CSet α β := M_mem_of_Good hT e heL hQ.1
    have hMd : S.M e (S.psi e π) e = d := by
      have h1 := M_mem_self hπ heL
      have h2 : S.psi (S.M e (S.psi e π) e) π = S.psi d π := (psi_M_eq hπ heL).trans hg
      have hc := compare_psi hπ h1 hd
      rw [h2, compare_eq_iff_eq.2 rfl] at hc
      exact compare_eq_iff_eq.1 hc.symm
    rw [← hMd]; exact hMmem

end InaccSeq

end Googology.Notation.InaccPsi
