import Googology.Trans.PoR.InaccPsi.R2.GhLoc

/-!
# THE CODE `ε_{Ω₁+1}·ω`: the union of all layers `ghB n a`, with top `Γ_{x+1+ε_{x+1}·ω}`

The layers `ghB n a` (`R2.GhTow`, codes `ε_{Ω₁+1}·(n+1) + a`, offsets `ε_{x+1}·(n+1) + a(x)`) for all `n < ω` and
`a < ε_{Ω₁+1}` form a union step (`R2.GhU`) with the offset `l(x) = ε_{x+1}·ω = ω^{ε_{x+1}+1}`: logend
`ε_{x+1} + 1` (Lemma IMG `RstK.pkg_eMt`), Lemma EXACT `π(ω^{ε_{ρ+1}+1}) = ω^{ε_{σ+1}+1}` (`pi_eAtomT`, at `υ`-points).

* `ghW_eq` (`ε_{x+1}·ω = ω^{ε_{x+1}+1}`), `ghW_lg`, `ghW_lt_gq0`, `ghW_pi`, `ghFW` (the data), `ghWB` (**THE GATED LAYER
  OF THE CODE `ε_{Ω₁+1}·ω`**: gate `0`, top `ϑˣ(Ω₁·Ω₁ + ε_{x+1}·ω) = Γ_{x+1+ε_{x+1}·ω}` at every `ε`-number base),
  `ghWB_top`.

Not located: its top reads the atom `Γ_{Ω₁+1+ε_{Ω₁+1}·ω} = ghV`, the bound of the atoms `ghAt` of `R2.GhAt`.

No new axiom.  New definitions: `ghFW`, `ghWB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf

theorem ghW_eq (x : Ordinal.{0}) : eN x * ω = ω ^ (eN x + 1) := by
  rw [opow_add, opow_one, show ω ^ eN x = eN x from eN_E x]

theorem ghW_lg (x : Ordinal.{0}) : lg (eN x * ω) = eN x + 1 := by
  have h := Ge.lg_add_opow (u := 0) (e := eN x + 1) (dvd_zero _)
  rwa [zero_add, ← ghW_eq] at h

theorem ghW_lt_gq0 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : eN x * ω < gq 0 x := by
  have hE := (gfq0_facts hx hx1).2.2.2
  exact hE.mul_lt (gh_eN_lt_gq0 hx hx1) (omega0_lt_inE hE)

/-- **Lemma EXACT for `ε_{x+1}·ω`** at `υ`-points. -/
theorem ghW_pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    eN ρ * ω ∈ TB ρ σ ∧ pi σ ρ (eN ρ * ω) = eN σ * ω := by
  have h1σ : (1 : Ordinal.{0}) < σ := lu_one_lt_E hB.1
  have h1e : (1 : Ordinal.{0}) < eN ρ := (lu_one_lt_E hB.2.1).trans (lt_eN ρ)
  obtain ⟨h1, h2⟩ := pi_eAtomT hσ hρ hB (gh_eN_pi hB).1 (mem_TB_of_lt hB h1σ) h1e
  rw [pi_lt hB h1σ] at h2
  rw [ghW_eq, ghW_eq]
  exact ⟨h1, h2⟩

theorem ghW_lim (x : Ordinal.{0}) : IsSuccLimit (eN x * ω) := by
  rw [ghW_eq]
  exact ⟨not_isMin_iff_ne_bot.2 (opow_pos _ omega0_pos).ne', isSuccPrelimit_iff_omega0_dvd.2
    (by
      calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
        _ ∣ ω ^ (eN x + 1) := opow_dvd_opow ω le_add_self)⟩

theorem ghBs_lt_W (n : ℕ) (x : Ordinal.{0}) : ghBs n x < eN x * ω :=
  (mul_lt_mul_iff_right₀ (eN_E x).pos).2 (natCast_lt_omega0 _)

/-- **The data of the union at the code `ε_{Ω₁+1}·ω`**: all layers `ghB n a`, the offset `ε_{x+1}·ω`, gate `0`. -/
noncomputable def ghFW : GhUF 0 where
  I := ℕ × {a : Ordinal.{0} // a < gfE}
  K := fun i => ghB i.1 i.2.1 i.2.2
  gi := fun i => gtc i.2.1
  o := fun i x => ghBs i.1 x + rdc i.2.1 x
  l := fun x => eN x * ω
  lp := fun _ => 0
  i0 := (0, ⟨0, eW_E.pos⟩)
  ip := (0, ⟨0, eW_E.pos⟩)
  g_le := fun i => (ghB_g i.1 i.2.2).le
  gi0 := gtc_zero
  gip := gtc_zero.le
  E_eq := fun i x hx hx1 hg => ghB_E i.1 i.2.2 hx hx1 hg
  o_lt := fun i x hx _ _ hg => by
    have h1 : ghBs i.1 x + rdc i.2.1 x < ghBs (i.1 + 1) x := by
      rw [ghBs_succ]; exact (add_lt_add_iff_left _).2 (rdc_lt_eN hx _ hg)
    exact h1.trans (ghBs_lt_W (i.1 + 1) x)
  l_lt := fun x hx hx1 _ => ghW_lt_gq0 hx hx1
  lim := fun x _ _ _ => ghW_lim x
  cof := fun x hx _ _ ν hν => by
    have hne : eN x ≠ 0 := (eN_E x).pos.ne'
    obtain ⟨m, hm⟩ := lt_omega0.1 ((Ordinal.div_lt hne).2 hν)
    refine ⟨(m, ⟨0, eW_E.pos⟩), by show gtc 0 < x; rw [gtc_zero]; exact hx.pos, ?_⟩
    show ν ≤ ghBs m x + rdc 0 x
    rw [rdc_zero, add_zero, ghBs]
    exact ((Ordinal.div_lt hne).1 (show ν / eN x < ((m + 1 : ℕ) : Ordinal.{0}) by
      rw [hm]; exact_mod_cast Nat.lt_succ_self m)).le
  pi := fun _ _ hσ hρ hB _ => ghW_pi hσ hρ hB
  dec := fun x _ _ _ => by
    refine ⟨?_, dvd_zero _, ?_⟩
    · show eN x * ω = 0 + ω ^ lg (eN x * ω)
      rw [ghW_lg, zero_add, ghW_eq]
    · show (0 : Ordinal.{0}) < eN x * ω
      rw [ghW_eq]; exact opow_pos _ omega0_pos
  lp_le := fun _ _ _ _ => zero_le
  pkg := fun ρ τ δ h hg => by
    have hcb : OT.CB (OT.k 1) ρ := lu_one_lt_E (upsPt_inE h.ρU)
    refine GhPkg.congr h (GhPkg.of_img (h.pkg_eMt 0 hcb (by simp))) (fun y _ _ _ => ?_) hg
    show eN y * nS 0 + OT.ev (OT.k 1) y = lg (eN y * ω)
    rw [ghW_lg, OT.ev_k]
    simp [nS]

/-- **THE GATED LAYER OF THE CODE `ε_{Ω₁+1}·ω`**: gate `0`, top `ϑˣ(Ω₁·Ω₁ + ε_{x+1}·ω) = Γ_{x+1+ε_{x+1}·ω}`. -/
noncomputable def ghWB : GdB := ghLimB ghFW

theorem ghWB_g : ghWB.g = 0 := rfl

theorem ghWB_E (x : Ordinal.{0}) : ghWB.K.E x = gq (eN x * ω) x := rfl

theorem ghWB_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : ghWB.K.sys.top x = gq (eN x * ω) x := by
  have hg : (0 : Ordinal.{0}) < x := hx.pos
  rw [ghWB.K.top_eq x hx hx1 hg, ghWB_E]
  exact (ghFW.top_facts hx hx1 hg).2.2.2.1

end Googology.Trans.PoR.InaccPsi.R2.Gh
