import Googology.Trans.PoR.InaccPsi.R2.RuOut

/-!
# The normal-form argument of a collapse below `ψ_κ(X)`; the offsets below `θ` need no argument `≥ Ω_ω`

`M = InaccSeq.M` (the least member of `Cl(b, ψ_κ(b))` at or above `b`), `θ = ψ_{Ω₂}(Ω_ω)`, `θ₂ = ψ_{Ω₃}(Ω_ω)`.

* `ryNf S κ b := M_{b, ψ_κ(b)}(b)` (**the normal-form argument**);
* `ryNf_spec` (**generic**): if `X` lies in every `Cl(a, c)` and `ψ_κ(b) < ψ_κ(X)`, then `d = ryNf S κ b` has
  `d < X`, `ψ_κ(d) = ψ_κ(b)`, `d ∈ Cl(d, ψ_κ(d))` and `d ∈ Cl(X, ψ_κ(d))` (every collapse that builds `d` above
  `ψ_κ(d)` has its argument `< X`);
* `ryNf_mem`: if moreover `κ ≤ Λ` and `ψ_κ(b) ∈ Cl(a, Z)` with `Z ≤ ψ_κ(b)`, then `d ∈ Cl(a, Z)` and `d < a`;
* `ryTh_nf`, `ryTh_nf_mem` (**the atoms of the offsets below `θ`**): every `ψ_{Ω₂}(b) < θ` is `ψ_{Ω₂}(d)` with
  `d < Ω_ω`, `d ∈ Cl(Ω_ω, ψ_{Ω₂}(d))`, and `d ∈ Cl(a, Z)`, `d < a` when `ψ_{Ω₂}(b) ∈ Cl(a, Z)`, `Z ≤ ψ_{Ω₂}(b)`;
* `ryObst` (**the obstruction of the previous round is not one of values**): `b₀ = ψ_{Ω₃}(Ω_ω·2)` has
  `θ₂ ≤ b₀`, its argument `Ω_ω·2` is above `Ω_ω + θ₂·(x+1)` for every `x < Ω_ω`, and still `ψ_{Ω₂}(b₀) < θ` and
  `ψ_{Ω₂}(b₀) = ψ_{Ω₂}(d)` with `d < Ω_ω`, `d ∈ Cl(Ω_ω, ψ_{Ω₂}(d))`.

So a lift of the offsets `ζ < θ` may be read on normal forms, where every argument is `< Ω_ω`; a lift that
commutes with `+` is not excluded by arguments `e ≥ Ω_ω·2` inside the terms of `ζ`.

No new axiom.  New definition: `ryNf`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ry

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-- **The normal-form argument** `M_{b, ψ_κ(b)}(b)`. -/
noncomputable def ryNf (S : InaccSeq.{0}) (κ b : Ordinal.{0}) : Ordinal.{0} := S.M b (S.psi b κ) b

/-- **The normal-form argument below `X`.** -/
theorem ryNf_spec {κ X b : Ordinal.{0}} (hκ : S.InR κ) (hX : ∀ a c, X ∈ S.CSet a c)
    (hb : S.psi b κ < S.psi X κ) :
    ryNf S κ b < X ∧ S.psi (ryNf S κ b) κ = S.psi b κ ∧
      ryNf S κ b ∈ S.CSet (ryNf S κ b) (S.psi (ryNf S κ b) κ) ∧
      ryNf S κ b ∈ S.CSet X (S.psi (ryNf S κ b) κ) := by
  unfold ryNf
  have hXL : X < S.Lam := lt_Lam_of_mem zero_le (hX 0 0)
  have hbX : b < X := by
    by_contra h
    push Not at h
    exact absurd (psi_mono hκ h).1 (not_le.2 hb)
  have hbL : b < S.Lam := hbX.trans hXL
  have hdX : S.M b (S.psi b κ) b ≤ X := M_le (hX _ _) hbX.le
  have heq : S.psi (S.M b (S.psi b κ) b) κ = S.psi b κ := psi_M_eq hκ hbL
  have hself := M_mem_self hκ hbL
  have hlt : S.M b (S.psi b κ) b < X := by
    refine lt_of_le_of_ne hdX fun h => ?_
    rw [← heq, h] at hb
    exact lt_irrefl _ hb
  exact ⟨hlt, heq, hself, CSet_mono hlt.le le_rfl hself⟩

/-- **The normal-form argument stays in the hull.** -/
theorem ryNf_mem {κ X b a Z : Ordinal.{0}} (hκ : S.InR κ) (hκL : κ ≤ S.Lam)
    (hX : ∀ a c, X ∈ S.CSet a c) (hb : S.psi b κ < S.psi X κ) (hmem : S.psi b κ ∈ S.CSet a Z) (hZ : Z ≤ S.psi b κ) :
    ryNf S κ b ∈ S.CSet a Z ∧ ryNf S κ b < a := by
  obtain ⟨-, heq, hself, -⟩ := ryNf_spec hκ hX hb
  have hZL : Z ≤ S.Lam := (hZ.trans (psi_lt hκ b).le).trans hκL
  refine arg_mem_of_psi_mem hκ ?_ ?_ hZL hself
  · rw [heq]; exact hmem
  · rw [heq]; exact hZ

theorem ryOmW_mem (a c : Ordinal.{0}) : Om ω ∈ S.CSet a c := ConjT.OmW_mem S a c

/-- **The atoms below `θ`**: `ψ_{Ω₂}(b) < θ` is `ψ_{Ω₂}(d)` with `d < Ω_ω` and `d ∈ Cl(Ω_ω, ψ_{Ω₂}(d))`. -/
theorem ryTh_nf {b : Ordinal.{0}} (hb : S.psi b (Om (1 + 1)) < ConjT.th S) :
    ∃ d, d < Om ω ∧ S.psi d (Om (1 + 1)) = S.psi b (Om (1 + 1)) ∧
      d ∈ S.CSet d (S.psi d (Om (1 + 1))) ∧ d ∈ S.CSet (Om ω) (S.psi d (Om (1 + 1))) :=
  ⟨_, ryNf_spec (InR_Om_succ 1) ryOmW_mem hb⟩

/-- **The atoms below `θ` in a hull**: the normal-form argument is in the hull, below `a` and below `Ω_ω`. -/
theorem ryTh_nf_mem {b a Z : Ordinal.{0}} (hb : S.psi b (Om (1 + 1)) < ConjT.th S)
    (hmem : S.psi b (Om (1 + 1)) ∈ S.CSet a Z) (hZ : Z ≤ S.psi b (Om (1 + 1))) :
    ∃ d, d < Om ω ∧ d < a ∧ S.psi d (Om (1 + 1)) = S.psi b (Om (1 + 1)) ∧ d ∈ S.CSet a Z ∧
      d ∈ S.CSet d (S.psi d (Om (1 + 1))) ∧ d ∈ S.CSet (Om ω) (S.psi d (Om (1 + 1))) := by
  obtain ⟨h1, h2, h3, h4⟩ := ryNf_spec (InR_Om_succ 1) ryOmW_mem hb
  have hκL : Om (1 + 1 : Ordinal.{0}) ≤ S.Lam := (lt_Lam_of_mem zero_le (Mx.mxOm2_mem (S := S) 0 0)).le
  obtain ⟨h5, h6⟩ := ryNf_mem (InR_Om_succ 1) hκL ryOmW_mem hb hmem hZ
  exact ⟨_, h1, h6, h2, h5, h3, h4⟩

theorem ryOm3_mem (a c : Ordinal.{0}) : Om (1 + 1 + 1 : Ordinal.{0}) ∈ S.CSet a c :=
  CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (CSet.one_mem a c)))

theorem ryOm3_lt : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := by
  refine Om_lt_Om.2 ?_
  have e : (1 + 1 + 1 : Ordinal.{0}) = ((3 : ℕ) : Ordinal.{0}) := by norm_num
  rw [e]; exact natCast_lt_omega0 3

/-- **The obstruction is not one of values**: `b₀ = ψ_{Ω₃}(Ω_ω·2)` is `≥ θ₂`, its argument `Ω_ω·2` exceeds every
`Ω_ω + θ₂·(x+1)` with `x < Ω_ω`, and `ψ_{Ω₂}(b₀) < θ` is `ψ_{Ω₂}(d)` with `d < Ω_ω`, `d ∈ Cl(Ω_ω, ψ_{Ω₂}(d))`. -/
theorem ryObst :
    Lc.lcTh S 2 ≤ S.psi (Om ω + Om ω) (Om (1 + 1 + 1)) ∧
      (∀ x, x < Om ω → Om ω + Lc.lcTh S 2 * (x + 1) < Om ω + Om ω) ∧
      S.psi (S.psi (Om ω + Om ω) (Om (1 + 1 + 1))) (Om (1 + 1)) < ConjT.th S ∧
      ∃ d, d < Om ω ∧
        S.psi d (Om (1 + 1)) = S.psi (S.psi (Om ω + Om ω) (Om (1 + 1 + 1))) (Om (1 + 1)) ∧
        d ∈ S.CSet (Om ω) (S.psi d (Om (1 + 1))) := by
  have hR3 : S.InR (Om (1 + 1 + 1 : Ordinal.{0})) := InR_Om_succ (1 + 1)
  have hW : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have h1 : Lc.lcTh S 2 ≤ S.psi (Om ω + Om ω) (Om (1 + 1 + 1)) := by
    have e : Lc.lcTh S 2 = S.psi (Om ω) (Om (1 + 1 + 1)) := by
      unfold Lc.lcTh; norm_num
    rw [e]; exact (psi_mono hR3 le_self_add).1
  have h2 : ∀ x, x < Om ω → Om ω + Lc.lcTh S 2 * (x + 1) < Om ω + Om ω := by
    intro x hx
    refine (add_lt_add_iff_left _).2 ?_
    have hth : Lc.lcTh S 2 < Om ω := by
      have e : Lc.lcTh S 2 = S.psi (Om ω) (Om (1 + 1 + 1)) := by
        unfold Lc.lcTh; norm_num
      rw [e]; exact (psi_lt hR3 _).trans ryOm3_lt
    have hP : IsPrincipal (· * ·) (Om (ω : Ordinal.{0})) := by
      have e := Low.opow_eq_self_of_SC hW
      have h := isPrincipal_mul_omega0_opow_opow (Om (ω : Ordinal.{0}))
      rwa [e, e] at h
    exact hP hth (hW.add_one_lt hx)
  have h3 : S.psi (S.psi (Om ω + Om ω) (Om (1 + 1 + 1))) (Om (1 + 1)) < ConjT.th S := by
    have hle : S.psi (S.psi (Om ω + Om ω) (Om (1 + 1 + 1))) (Om (1 + 1)) ≤
        S.psi (Om (1 + 1 + 1)) (Om (1 + 1)) := (psi_mono (InR_Om_succ 1) (psi_lt hR3 _).le).1
    refine hle.trans_lt ?_
    exact psi_lt_psi_of_mem (InR_Om_succ 1) ryOm3_lt (ryOm3_mem _ _)
  obtain ⟨d, hd, he, -, hc⟩ := ryTh_nf h3
  exact ⟨h1, h2, h3, d, hd, he, hc⟩

end Googology.Trans.PoR.InaccPsi.R2.Ry
