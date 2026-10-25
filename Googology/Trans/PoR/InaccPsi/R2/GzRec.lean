import Googology.Trans.PoR.InaccPsi.R2.GzY

/-!
# THE RECURSION OF THE STAGE `n`: ALL INDICES IN `[ζ_{G+n+1}, ζ_{G+n+2})`, FROM ANY SELF-READ START

`R2.GwYRec` (`Gw.gwYD`) is the recursion over the indices in `[ζ_{G+1}, ζ_{G+2})` from the union `Gw.gwZU`.  Here the
same recursion for every `n`, from ANY start `U0` with `GzStart n U0` (a `GwZD` with `N = n + 1`, index `ζ_{G+n+1}`,
base gate `0`, base reading `Z_{n+1}(x) = ζ_{Γ_{x+1}+n+1}`): `gzYD n U0 d` (`d < ζ_{G+n+2}`) has the bound
`ε_{ζ_{G+n+1}+d} = φ(1, ζ_{G+n+1} + d)`; `gzYD n U0 0 = U0`, `gzYD n U0 (d+1)` is the step, and at a limit `λ` it is
the union `Gz.GzFam.U` of all `gzYD n U0 μ`, `μ < λ`, with the index `λ` read by the first system containing it as a
code (`Gz.gzY_cover`).  The invariant (`GzInv`, `gz_inv`): index `ζ_{G+n+1} + μ`, `N = n + 1`, coherence, base reading
`φ(1, Z_{n+1}(x) + μ(x))` above the base gate, `γ(gzYD μ) < x ⇔ g(μ) < x`.

* `GzStart`, `GzInv`, `gzYIdx`, `gzFamOf`, `gzExt`, `gzLimD`, `gzYD` (**THE RECURSION OF THE STAGE `n`**),
  `gzYD_zero`, `gzYD_succ`, `gzYD_limit`, `GzTop`, `gz_inv` (**THE INVARIANT AT EVERY INDEX BELOW `ζ_{G+n+2}`**);
* `gz_ix`, `gz_N`, `gz_B`, `gz_b`, `gz_γ_iff`, `gz_self`, `gz_ext`.

No new axiom.  New definitions: `GzStart`, `GzInv`, `GzTop`, `gzYIdx`, `gzFamOf`, `gzExt`, `gzLimD`, `gzYD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gz

open Googology.Trans.PoR.InaccPsi.R2.Gw

open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The start and the invariant -/

/-- **The start of the stage `n`**: a union at the index `ζ_{G+n+1}` reading its own index (`N = n + 1`, base gate
`0`, base reading `Z_{n+1}(x)`). -/
structure GzStart (n : ℕ) (U0 : GwZD) : Prop where
  N : U0.N = n + 1
  ix : U0.ix = gzZ (n + 1)
  γ : U0.γ = 0
  b : ∀ x, U0.b x = gwZn x (n + 1)

/-- **The invariant of a family below `λ`.** -/
structure GzInv (n : ℕ) (U0 : GwZD) (l : Ordinal.{0}) (F : Ordinal.{0} → GwZD) : Prop where
  ix : ∀ μ, μ < l → (F μ).ix = gzZ (n + 1) + μ
  zero : 0 < l → F 0 = U0
  γ0 : 0 < l → (F 0).γ = 0
  succ : ∀ μ, μ + 1 < l → F (μ + 1) = (F μ).step
  N : ∀ μ, μ < l → (F μ).N = n + 1
  cohR : ∀ β γ, β ≤ γ → γ < l → ∀ c x, c < (F β).B → (F γ).R c x = (F β).R c x
  cohg : ∀ β γ, β ≤ γ → γ < l → ∀ c, c < (F β).B → (F γ).g c = (F β).g c
  hb : ∀ μ, μ < l → ∀ x, InE x → x < Om1 → (F μ).γ < x → (F μ).b x = veblen 1 (gwZn x (n + 1) + (F μ).R μ x)
  hγ : ∀ μ, μ < l → ∀ x, InE x → x < Om1 → ((F μ).γ < x ↔ (F μ).g μ < x)

namespace GzInv

variable {n : ℕ} {U0 : GwZD} {l : Ordinal.{0}} {F : Ordinal.{0} → GwZD} (H : GzInv n U0 l F)
include H

theorem B_eq {β : Ordinal.{0}} (h : β < l) : (F β).B = veblen 1 (gzZ (n + 1) + β) := by
  rw [(F β).B_ix, H.ix β h]

theorem B_le {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (h : γ < l) : (F β).B ≤ (F γ).B := by
  rw [H.B_eq (lt_of_le_of_lt hβγ h), H.B_eq h]
  exact (isNormal_veblen 1).monotone ((add_le_add_iff_left _).2 hβγ)

theorem self_lt {μ : Ordinal.{0}} (h : μ < l) (hZ : μ < gzZ (n + 2)) : μ < (F μ).B := by
  rw [H.B_eq h]; exact gzY_self_lt (n + 1) hZ

/-- The reading of a code `μ` is the same in every member containing it. -/
theorem R_tr {μ d : Ordinal.{0}} (hμ : μ < l) (hd : d < l) (hμd : μ < (F d).B) (hμB : μ < (F μ).B)
    (x : Ordinal.{0}) : (F d).R μ x = (F μ).R μ x := by
  rcases le_total μ d with h | h
  · exact H.cohR μ d h hd μ x hμB
  · exact (H.cohR d μ h hμ μ x hμd).symm

theorem g_tr {μ d : Ordinal.{0}} (hμ : μ < l) (hd : d < l) (hμd : μ < (F d).B) (hμB : μ < (F μ).B) :
    (F d).g μ = (F μ).g μ := by
  rcases le_total μ d with h | h
  · exact H.cohg μ d h hd μ hμB
  · exact (H.cohg d μ h hμ μ hμd).symm

theorem congr {G : Ordinal.{0} → GwZD} (hFG : ∀ β, β < l → G β = F β) : GzInv n U0 l G where
  ix := fun β h => by rw [hFG β h]; exact H.ix β h
  zero := fun h => by rw [hFG 0 h]; exact H.zero h
  γ0 := fun h => by rw [hFG 0 h]; exact H.γ0 h
  succ := fun μ h => by rw [hFG (μ + 1) h, hFG μ ((lt_add_one μ).trans h)]; exact H.succ μ h
  N := fun μ h => by rw [hFG μ h]; exact H.N μ h
  cohR := fun β γ hβγ h c x hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohR β γ hβγ h c x hc
  cohg := fun β γ hβγ h c hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohg β γ hβγ h c hc
  hb := fun μ h x hx hx1 => by rw [hFG μ h]; exact H.hb μ h x hx hx1
  hγ := fun μ h x hx hx1 => by rw [hFG μ h]; exact H.hγ μ h x hx hx1

end GzInv

theorem gzInv_zero (n : ℕ) (U0 : GwZD) (F : Ordinal.{0} → GwZD) : GzInv n U0 0 F where
  ix := fun _ h => absurd h (not_lt.2 zero_le)
  zero := fun h => absurd h (lt_irrefl 0)
  γ0 := fun h => absurd h (lt_irrefl 0)
  succ := fun μ h => absurd h (not_lt.2 zero_le)
  N := fun _ h => absurd h (not_lt.2 zero_le)
  cohR := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ _ _ h => absurd h (not_lt.2 zero_le)
  hb := fun _ h => absurd h (not_lt.2 zero_le)
  hγ := fun _ h => absurd h (not_lt.2 zero_le)

/-! ## The family at a limit -/

section Fam

variable (n : ℕ) (U0 : GwZD)

/-- The first member that contains the index `λ` as a code (the index system of the union). -/
noncomputable def gzYIdx (l : Ordinal.{0}) (F : Ordinal.{0} → GwZD) : Ordinal.{0} :=
  sInf {d | d < l ∧ l < (F d).B}

variable {n U0}

theorem gzYIdx_spec {l : Ordinal.{0}} {F : Ordinal.{0} → GwZD} (hl : IsSuccLimit l) (hlZ : l < gzZ (n + 2))
    (H : GzInv n U0 l F) : gzYIdx l F < l ∧ l < (F (gzYIdx l F)).B := by
  obtain ⟨d, hd, hld⟩ := gzY_cover (n + 1) hl.bot_lt hlZ
  have h : l < (F d).B := by rw [H.B_eq hd]; exact hld
  exact csInf_mem (s := {d | d < l ∧ l < (F d).B}) ⟨d, hd, h⟩

variable (n U0)

/-- **The family over all `μ < λ`**, its indices read by the first member containing `λ`. -/
noncomputable def gzFamOf (l : Ordinal.{0}) (hl : IsSuccLimit l) (hlZ : l < gzZ (n + 2)) (F : Ordinal.{0} → GwZD)
    (H : GzInv n U0 l F) : GzFam n where
  E := F (gzYIdx l F)
  l := l
  F := F
  l_lim := hl
  l_lt := (gzYIdx_spec hl hlZ H).2
  l_Z := hlZ
  EN := H.N _ (gzYIdx_spec hl hlZ H).1
  hN := H.N
  ix := H.ix
  γ0 := H.γ0 hl.bot_lt
  succ := H.succ
  cohR := H.cohR
  cohg := H.cohg
  hb := fun μ hμ x hx hx1 hγ => by
    obtain ⟨hd, hld⟩ := gzYIdx_spec hl hlZ H
    rw [H.hb μ hμ x hx hx1 hγ, H.R_tr hμ hd (hμ.trans hld) (H.self_lt hμ (hμ.trans hlZ)) x]
  hγ := fun μ hμ x hx hx1 => by
    obtain ⟨hd, hld⟩ := gzYIdx_spec hl hlZ H
    rw [H.hγ μ hμ x hx hx1, H.g_tr hμ hd (hμ.trans hld) (H.self_lt hμ (hμ.trans hlZ))]

/-- The family of the earlier values, extended by the start. -/
noncomputable def gzExt (l : Ordinal.{0}) (IH : ∀ β, β < l → GwZD) (β : Ordinal.{0}) : GwZD :=
  if h : β < l then IH β h else U0

open Classical in
/-- The limit step: the union over all smaller indices when the invariant holds. -/
noncomputable def gzLimD (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ β, β < l → GwZD) : GwZD :=
  if H : l < gzZ (n + 2) ∧ GzInv n U0 l (gzExt U0 l IH) then (gzFamOf n U0 l hl H.1 (gzExt U0 l IH) H.2).U else U0

/-- **THE RECURSION OF THE STAGE `n`**: the start `U0` at `0`, the step at `c+1`, the union over all `μ < λ` at a
limit `λ`; `gzYD n U0 d` has the bound `ε_{ζ_{G+n+1}+d}`. -/
noncomputable def gzYD (ν : Ordinal.{0}) : GwZD :=
  Ordinal.limitRecOn (motive := fun _ => GwZD) ν U0 (fun _ D => D.step) (gzLimD n U0)

theorem gzYD_zero : gzYD n U0 0 = U0 := by
  unfold gzYD; rw [Ordinal.limitRecOn_zero]

theorem gzYD_succ (ν : Ordinal.{0}) : gzYD n U0 (ν + 1) = (gzYD n U0 ν).step := by
  unfold gzYD; rw [Ordinal.limitRecOn_add_one]

theorem gzYD_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    gzYD n U0 l = gzLimD n U0 l hl (fun β _ => gzYD n U0 β) := by
  unfold gzYD; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem gzExt_eq {l β : Ordinal.{0}} (h : β < l) : gzExt U0 l (fun β _ => gzYD n U0 β) β = gzYD n U0 β := by
  unfold gzExt; rw [dif_pos h]

end Fam

/-! ## The invariant at every index -/

/-- The new facts at the top `ν`. -/
structure GzTop (n : ℕ) (U0 : GwZD) (ν : Ordinal.{0}) : Prop where
  ix : (gzYD n U0 ν).ix = gzZ (n + 1) + ν
  N : (gzYD n U0 ν).N = n + 1
  cohR : ∀ β, β < ν → ∀ c x, c < (gzYD n U0 β).B → (gzYD n U0 ν).R c x = (gzYD n U0 β).R c x
  cohg : ∀ β, β < ν → ∀ c, c < (gzYD n U0 β).B → (gzYD n U0 ν).g c = (gzYD n U0 β).g c
  hb : ∀ x, InE x → x < Om1 → (gzYD n U0 ν).γ < x →
    (gzYD n U0 ν).b x = veblen 1 (gwZn x (n + 1) + (gzYD n U0 ν).R ν x)
  hγ : ∀ x, InE x → x < Om1 → ((gzYD n U0 ν).γ < x ↔ (gzYD n U0 ν).g ν < x)

section Inv

variable {n : ℕ} {U0 : GwZD} (hU : GzStart n U0)
include hU

theorem gzInv_succ {ν : Ordinal.{0}} (H : GzInv n U0 ν (gzYD n U0)) (T : GzTop n U0 ν) :
    GzInv n U0 (ν + 1) (gzYD n U0) where
  ix := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.ix β h'
    · exact T.ix
  N := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.N β h'
    · exact T.N
  zero := fun _ => gzYD_zero n U0
  γ0 := fun _ => by rw [gzYD_zero]; exact hU.γ
  succ := fun μ _ => gzYD_succ n U0 μ
  cohR := fun β γ hβγ h c x hc => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.cohR β γ hβγ h' c x hc
    · rcases hβγ.lt_or_eq with h'' | rfl
      · exact T.cohR β h'' c x hc
      · rfl
  cohg := fun β γ hβγ h c hc => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.cohg β γ hβγ h' c hc
    · rcases hβγ.lt_or_eq with h'' | rfl
      · exact T.cohg β h'' c hc
      · rfl
  hb := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.hb β h'
    · exact T.hb
  hγ := fun β h => by
    rcases (Order.lt_add_one_iff.1 h).lt_or_eq with h' | rfl
    · exact H.hγ β h'
    · exact T.hγ

theorem gzInv_lim {l : Ordinal.{0}} (IH : ∀ β, β < l → GzInv n U0 (β + 1) (gzYD n U0)) :
    GzInv n U0 l (gzYD n U0) where
  ix := fun β h => (IH β h).ix β (lt_add_one β)
  N := fun β h => (IH β h).N β (lt_add_one β)
  zero := fun _ => gzYD_zero n U0
  γ0 := fun _ => by rw [gzYD_zero]; exact hU.γ
  succ := fun μ _ => gzYD_succ n U0 μ
  cohR := fun β γ hβγ h => (IH γ h).cohR β γ hβγ (lt_add_one γ)
  cohg := fun β γ hβγ h => (IH γ h).cohg β γ hβγ (lt_add_one γ)
  hb := fun β h => (IH β h).hb β (lt_add_one β)
  hγ := fun β h => (IH β h).hγ β (lt_add_one β)

theorem gzTop_zero : GzTop n U0 0 where
  ix := by rw [gzYD_zero, add_zero]; exact hU.ix
  N := by rw [gzYD_zero]; exact hU.N
  cohR := fun _ h => absurd h (not_lt.2 zero_le)
  cohg := fun _ h => absurd h (not_lt.2 zero_le)
  hb := fun x _ _ _ => by
    rw [gzYD_zero, U0.R_zero, add_zero, hU.b]
    show evZ (gwZn x n) = veblen 1 (evZ (gwZn x n))
    exact (epsilon_evZ _).symm
  hγ := fun x _ _ => by rw [gzYD_zero, U0.g_zero, hU.γ]

omit hU in
theorem gzTop_succ {ν : Ordinal.{0}} (hνZ : ν < gzZ (n + 2)) (H : GzInv n U0 (ν + 1) (gzYD n U0)) :
    GzTop n U0 (ν + 1) where
  ix := by
    rw [gzYD_succ]
    show (gzYD n U0 ν).step.ix = _
    rw [GwZD.step_ix, H.ix ν (lt_add_one ν), add_assoc]
  N := by
    rw [gzYD_succ]
    show (gzYD n U0 ν).step.N = n + 1
    rw [GwZD.step_N]; exact H.N ν (lt_add_one ν)
  cohR := fun β hβ c x hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [gzYD_succ]
    show (gzYD n U0 ν).step.R c x = _
    rw [GwZD.step_R_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν))) x]
    exact H.cohR β ν hβν (lt_add_one ν) c x hc
  cohg := fun β hβ c hc => by
    have hβν : β ≤ ν := Order.lt_add_one_iff.1 hβ
    rw [gzYD_succ]
    show (gzYD n U0 ν).step.g c = _
    rw [GwZD.step_g_low _ (hc.trans_le (H.B_le hβν (lt_add_one ν)))]
    exact H.cohg β ν hβν (lt_add_one ν) c hc
  hb := fun x hx hx1 hγx => by
    have hνB : ν < (gzYD n U0 ν).B := H.self_lt (lt_add_one ν) hνZ
    have hν1B : ν + 1 < (gzYD n U0 ν).B := (gzYD n U0 ν).B_lim.add_one_lt hνB
    have hγ : (gzYD n U0 ν).γ < x := by rw [gzYD_succ] at hγx; exact hγx
    rw [gzYD_succ]
    show (gzYD n U0 ν).step.b x = veblen 1 (gwZn x (n + 1) + (gzYD n U0 ν).step.R (ν + 1) x)
    rw [GwZD.step_b, GwZD.step_R_low _ hν1B x, (gzYD n U0 ν).R_succ, H.hb ν (lt_add_one ν) x hx hx1 hγ, go_eN_veb,
      add_assoc]
  hγ := fun x hx hx1 => by
    have hνB : ν < (gzYD n U0 ν).B := H.self_lt (lt_add_one ν) hνZ
    have hν1B : ν + 1 < (gzYD n U0 ν).B := (gzYD n U0 ν).B_lim.add_one_lt hνB
    rw [gzYD_succ]
    show (gzYD n U0 ν).γ < x ↔ (gzYD n U0 ν).step.g (ν + 1) < x
    rw [GwZD.step_g_low _ hν1B, H.hγ ν (lt_add_one ν) x hx hx1]
    exact ⟨fun h => (gzYD n U0 ν).g_succ x (ev_isSuccLimit_of_inE hx) ν hν1B h,
      fun h => ((gzYD n U0 ν).g_le_succ ν).trans_lt h⟩

omit hU in
theorem gzYD_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlZ : l < gzZ (n + 2)) (H : GzInv n U0 l (gzYD n U0)) :
    gzYD n U0 l = (gzFamOf n U0 l hl hlZ (gzExt U0 l fun β _ => gzYD n U0 β)
      (H.congr fun β h => gzExt_eq n U0 h)).U := by
  rw [gzYD_limit n U0 hl]; unfold gzLimD; rw [dif_pos ⟨hlZ, H.congr fun β h => gzExt_eq n U0 h⟩]

omit hU in
theorem gzTop_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlZ : l < gzZ (n + 2)) (H : GzInv n U0 l (gzYD n U0)) :
    GzTop n U0 l := by
  set Q := gzFamOf n U0 l hl hlZ (gzExt U0 l fun β _ => gzYD n U0 β) (H.congr fun β h => gzExt_eq n U0 h)
    with hQ
  have e : gzYD n U0 l = Q.U := gzYD_lim_eq hl hlZ H
  have hF : ∀ β, β < l → Q.F β = gzYD n U0 β := fun β h => gzExt_eq n U0 h
  have hl' : Q.l = l := rfl
  obtain ⟨hd, hld⟩ := gzYIdx_spec hl hlZ (H.congr fun β h => gzExt_eq n U0 h)
  have hE : Q.E = Q.F (gzYIdx l (gzExt U0 l fun β _ => gzYD n U0 β)) := rfl
  refine ⟨?_, ?_, fun β hβ c x hc => ?_, fun β hβ c hc => ?_, fun x hx hx1 hγx => ?_, fun x hx hx1 => ?_⟩
  · rw [e]; rfl
  · rw [e]; rfl
  · rw [e, Q.U_R (hl'.symm ▸ hβ) (by rw [hF β hβ]; exact hc) x, hF β hβ]
  · rw [e, Q.U_g (hl'.symm ▸ hβ) (by rw [hF β hβ]; exact hc), hF β hβ]
  · rw [e] at hγx ⊢
    rw [Q.U_b, Q.U_R hd hld x, hE]
    rfl
  · rw [e, Q.U_γ, Q.U_g hd hld, hE]
    rfl

/-- **THE INVARIANT AT EVERY INDEX `ν < ζ_{G+n+2}`.** -/
theorem gz_inv : ∀ ν : Ordinal.{0}, ν < gzZ (n + 2) → GzInv n U0 (ν + 1) (gzYD n U0) := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero => intro _; exact gzInv_succ hU (gzInv_zero n U0 _) (gzTop_zero hU)
  | add_one μ ih =>
    intro hν
    have hμ : μ < gzZ (n + 2) := (lt_add_one μ).trans hν
    have H := ih hμ
    exact gzInv_succ hU H (gzTop_succ hμ H)
  | limit l hl ih =>
    intro hν
    have H := gzInv_lim hU (fun β hβ => ih β hβ (hβ.trans hν))
    exact gzInv_succ hU H (gzTop_lim hl hν H)

end Inv

/-! ## The main facts -/

section Main

variable {n : ℕ} {U0 : GwZD} (hU : GzStart n U0) {ν : Ordinal.{0}} (hν : ν < gzZ (n + 2))
include hU hν

theorem gz_ix : (gzYD n U0 ν).ix = gzZ (n + 1) + ν := (gz_inv hU ν hν).ix ν (lt_add_one ν)

theorem gz_N : (gzYD n U0 ν).N = n + 1 := (gz_inv hU ν hν).N ν (lt_add_one ν)

/-- **The bound of `gzYD n U0 ν` is `ε_{ζ_{G+n+1}+ν}`.** -/
theorem gz_B : (gzYD n U0 ν).B = veblen 1 (gzZ (n + 1) + ν) := (gz_inv hU ν hν).B_eq (lt_add_one ν)

/-- **The base reading of `gzYD n U0 ν` is `φ(1, Z_{n+1}(x) + ν(x))`** above its gate. -/
theorem gz_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγx : (gzYD n U0 ν).γ < x) :
    (gzYD n U0 ν).b x = veblen 1 (gwZn x (n + 1) + (gzYD n U0 ν).R ν x) :=
  (gz_inv hU ν hν).hb ν (lt_add_one ν) x hx hx1 hγx

/-- **The base gate of `gzYD n U0 ν` lies below an `ε`-number `x` iff the gate of the code `ν` does.** -/
theorem gz_γ_iff {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (gzYD n U0 ν).γ < x ↔ (gzYD n U0 ν).g ν < x :=
  (gz_inv hU ν hν).hγ ν (lt_add_one ν) x hx hx1

theorem gz_self : ν < (gzYD n U0 ν).B := by rw [gz_B hU hν]; exact gzY_self_lt (n + 1) hν

end Main

/-- **Later systems extend earlier ones** (readings and gates). -/
theorem gz_ext {n : ℕ} {U0 : GwZD} (hU : GzStart n U0) {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < gzZ (n + 2)) :
    (∀ c x, c < (gzYD n U0 β).B → (gzYD n U0 γ).R c x = (gzYD n U0 β).R c x) ∧
    (∀ c, c < (gzYD n U0 β).B → (gzYD n U0 γ).g c = (gzYD n U0 β).g c) :=
  ⟨(gz_inv hU γ hγ).cohR β γ hβγ (lt_add_one γ), (gz_inv hU γ hγ).cohg β γ hβγ (lt_add_one γ)⟩

end Googology.Trans.PoR.InaccPsi.R2.Gz
