import Googology.Trans.PoR.InaccPsi.R2.HaSU

/-!
# HaL: ONE RECURSION OVER EVERY `ζ`-INDEX `λ < φ(3, G+1)`, THE `ζ`-INDEX A GATED CODE READ BY AN EARLIER SYSTEM

`Gz.gzLU` reads the `ζ`-index `λ` of a stage as a constant (`λ < ε₀`, below every base); at `λ = ε₀` this fails
(`Gz.gz_wall_e0`).  Here the `ζ`-index is a CODE: `haLU λ` (`λ < φ(3, G+1)`) is the start of the stage `λ`
(index base `Q_λ = φ(2, G + 1 + λ)`), and the stage parameters are `Ha.haPBof (haLU λ) λ` (`λ` read by the start
itself: `λ < Q_λ`), so the reading `P_λ(x) = φ(2, i₀(x) + λ(x))` and the stage gate `g(λ)` come from the systems:

* `haLU 0 = GzVD.ofW gwZU` (the union at `ζ_{G+1}`);
* `haLU (λ+1)` is the self-read union `Ha.haSU` of the gated stage `λ` started at `haLU λ`;
* at a limit `λ`, `haLU λ` is the union of all `haLU μ`, `μ < λ` (`HaLFam.U`): bound `Q_λ`, base gate `g(λ)`, base
  reading `P_λ(x)`, bound field `Zst_λ(x)`, where `λ` is read by the first earlier start containing it
  (`λ < Q_μ` for some `μ < λ`, `ha_cover`).  The readings of the codes below `Q_λ` lie below `P_λ(x)` because every
  code lies in a start with base gate below the base (`HaLFam.small`: a code `c ∈ [Q_μ, Q_{μ+1})` with gate below `σ`
  forces the gate of the start `μ+1` below `σ`, `Ha.haSU_high_gate`) and `P_μ(x) < P_λ(x)` for `μ < λ` above the
  gates (`HaLFam.b_le`); the bound fields `Zst_μ ≤ Zst_λ` (`HaLFam.Z_le`) carry the same invariant.

The invariant (`HaLInv`, `ha_inv`, every `ν < φ(3, G+1)`): bound `Q_μ`, start of the stage `μ`, the high-gate
property of the starts at successors, coherence of readings and gates.

* `haT` (`= φ(3, G+1)`), `ha_j`, `ha_cover`, `HaLInv`, `HaLFam`, `HaLFam.U` (**THE UNION AT A LIMIT `ζ`-INDEX**),
  `HaLFam.U_start`, `haLStep`, `haLExt`, `haLLimD`, `haLU` (**THE RECURSION**), `ha_inv` (**THE INVARIANT**),
  `haLU_B`, `haLU_start`, `haLU_γ_iff`, `haLD` (the systems of the stage `λ`), `haLD_B`.

No new axiom.  New definitions: `haT`, `HaLInv`, `HaLFam`, `HaLFam.BU`, `HaLFam.N`, `HaLFam.R`, `HaLFam.g`,
`HaLFam.E`, `HaLFam.Bp`, `HaLFam.U`, `haLStep`, `haLExt`, `haLLimD`, `haLU`, `haLPB`, `haLD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ha

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The bound `φ(3, G+1)` -/

/-- **`φ(3, G + 1)`**, the least fixed point of `φ(2, ·)` above `G = Γ_{Ω₁+1}`. -/
noncomputable def haT : Ordinal.{0} := veblen 3 (gcG 0 + 1)

theorem ha_two_lt_three : (2 : Ordinal.{0}) < 3 := by
  have : ((2 : ℕ) : Ordinal.{0}) < ((3 : ℕ) : Ordinal.{0}) := Nat.cast_lt.2 (by omega)
  exact_mod_cast this

theorem haT_fix : veblen 2 haT = haT := veblen_veblen_of_lt ha_two_lt_three _

theorem haT_E : InE haT := gg_veblen_eps three_ne_zero

theorem ha_G1_lt_T : gcG 0 + 1 < haT := by
  rcases (right_le_veblen 3 (gcG 0 + 1)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hl : IsSuccLimit haT := ev_isSuccLimit_of_inE haT_E
    rw [haT, ← h, ← Order.succ_eq_add_one] at hl
    exact Order.not_isSuccLimit_succ _ hl

theorem ha_add_lt_T {l : Ordinal.{0}} (hl : l < haT) : gcG 0 + 1 + l < haT :=
  (inE_indec haT_E).add_lt ha_G1_lt_T hl

/-- **`G + 1 + λ` is not a fixed point of `φ(2, ·)`** for `λ < φ(3, G+1)`. -/
theorem ha_j {l : Ordinal.{0}} (hl : l < haT) : gcG 0 + 1 + l < veblen 2 (gcG 0 + 1 + l) := by
  set y := gcG 0 + 1 + l with hy
  rcases (right_le_veblen 2 y).lt_or_eq with h | h
  · exact h
  · exfalso
    have hfix : ∀ b < (3 : Ordinal.{0}), veblen b y = y := by
      intro b hb
      rcases lt_or_ge b 2 with hb2 | hb2
      · conv_lhs => rw [h]
        rw [veblen_veblen_of_lt hb2]; exact h.symm
      · have : b = 2 := le_antisymm (Order.lt_add_one_iff.1 (by
          have e : (2 : Ordinal.{0}) + 1 = 3 := by
            have : ((2 : ℕ) : Ordinal.{0}) + 1 = ((3 : ℕ) : Ordinal.{0}) := by push_cast; rfl
            exact_mod_cast this
          rw [e]; exact hb)) hb2
        rw [this]; exact h.symm
    obtain ⟨z, hz⟩ := (mem_range_veblen three_ne_zero).2 hfix
    have hyT : y < haT := ha_add_lt_T hl
    rw [← hz, haT] at hyT
    have hzG : z < gcG 0 + 1 := (veblen_lt_veblen_iff_right (o := 3)).1 hyT
    have h3G : (3 : Ordinal.{0}) < gcG 0 := by
      have : ((3 : ℕ) : Ordinal.{0}) < gcG 0 := (natCast_lt_omega0 3).trans (omega0_lt_inE gr_G_inE)
      exact_mod_cast this
    have hle : y ≤ gcG 0 := by
      rw [← hz, ← gn_veb_fix (gcG_SC 0) h3G]
      exact (isNormal_veblen 3).monotone (Order.lt_add_one_iff.1 hzG)
    exact absurd (hle.trans_lt (lt_add_one (gcG 0))) (not_lt.2 (le_self_add))

theorem ha_lt_Q {l : Ordinal.{0}} (hl : l < haT) : l < veblen 2 (gcG 0 + 1 + l) :=
  le_add_self.trans_lt (ha_j hl)

theorem ha_Q_lt_T {l : Ordinal.{0}} (hl : l < haT) : veblen 2 (gcG 0 + 1 + l) < haT := by
  have h := (isNormal_veblen 2).strictMono (ha_add_lt_T hl)
  rwa [haT_fix] at h

/-- **A limit `λ < φ(3, G+1)` lies below `Q_μ` for some `μ < λ`.** -/
theorem ha_cover {l : Ordinal.{0}} (hl : IsSuccLimit l) (hlT : l < haT) :
    ∃ μ, μ < l ∧ l < veblen 2 (gcG 0 + 1 + μ) := by
  have h := ha_lt_Q hlT
  obtain ⟨t, ht, hlt⟩ := ((isNormal_veblen 2).lt_iff_exists_lt (isSuccLimit_add _ hl)).1 h
  obtain ⟨d, hd, htd⟩ := (lt_add_iff hl.bot_lt.ne').1 ht
  exact ⟨d, hd, hlt.trans_le ((isNormal_veblen 2).monotone htd)⟩

theorem ha_Q_lt_Q {μ l : Ordinal.{0}} (h : μ < l) : veblen 2 (gcG 0 + 1 + μ) < veblen 2 (gcG 0 + 1 + l) :=
  (isNormal_veblen 2).strictMono ((add_lt_add_iff_left _).2 h)

/-! ## The invariant -/

/-- **The invariant of the starts below `λ`.** -/
structure HaLInv (l : Ordinal.{0}) (F : Ordinal.{0} → GzVD) : Prop where
  B : ∀ μ, μ < l → (F μ).B = veblen 2 (gcG 0 + 1 + μ)
  st : ∀ μ (hμ : μ < haT), μ < l → ∀ h2 : μ < (F μ).B, HaSStart (haPBof (F μ) μ h2 (ha_j hμ)) (F μ)
  high : ∀ μ, μ + 1 < l → ∀ c σ, (F μ).B ≤ c → c < (F (μ + 1)).B → InE σ → σ < Om1 →
    (F (μ + 1)).g c < σ → (F (μ + 1)).γ < σ
  cohR : ∀ β γ, β ≤ γ → γ < l → ∀ c x, c < (F β).B → (F γ).R c x = (F β).R c x
  cohg : ∀ β γ, β ≤ γ → γ < l → ∀ c, c < (F β).B → (F γ).g c = (F β).g c

theorem ha_st_congr {D D' : GzVD} (e : D = D') {μ : Ordinal.{0}} (h2 : μ < D.B)
    (hj : gcG 0 + 1 + μ < veblen 2 (gcG 0 + 1 + μ))
    (h : ∀ h2' : μ < D'.B, HaSStart (haPBof D' μ h2' hj) D') : HaSStart (haPBof D μ h2 hj) D := by
  subst e; exact h h2

namespace HaLInv

variable {l : Ordinal.{0}} {F : Ordinal.{0} → GzVD} (H : HaLInv l F)
include H

theorem self_lt {μ : Ordinal.{0}} (h : μ < l) (hT : μ < haT) : μ < (F μ).B := by
  rw [H.B μ h]; exact ha_lt_Q hT

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

theorem congr {G : Ordinal.{0} → GzVD} (hFG : ∀ β, β < l → G β = F β) : HaLInv l G where
  B := fun μ h => by rw [hFG μ h]; exact H.B μ h
  st := fun μ hμ h h2 => ha_st_congr (hFG μ h) h2 (ha_j hμ) (H.st μ hμ h)
  high := fun μ h c σ h1 h2 hσ hσ1 hg => by
    rw [hFG (μ + 1) h] at h2 hg ⊢
    rw [hFG μ ((lt_add_one μ).trans h)] at h1
    exact H.high μ h c σ h1 h2 hσ hσ1 hg
  cohR := fun β γ hβγ h c x hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohR β γ hβγ h c x hc
  cohg := fun β γ hβγ h c hc => by
    rw [hFG β (lt_of_le_of_lt hβγ h)] at hc ⊢
    rw [hFG γ h]; exact H.cohg β γ hβγ h c hc

end HaLInv

/-! ## The union at a limit `ζ`-index -/

/-- **The family of all starts below a limit `λ < φ(3, G+1)`.** -/
structure HaLFam where
  l : Ordinal.{0}
  F : Ordinal.{0} → GzVD
  l_lim : IsSuccLimit l
  l_lt : l < haT
  H : HaLInv l F

namespace HaLFam

variable (L : HaLFam)

theorem lt_T {μ : Ordinal.{0}} (h : μ < L.l) : μ < haT := h.trans L.l_lt

/-- The bound of the union, `Q_λ = φ(2, G + 1 + λ)`. -/
noncomputable def BU : Ordinal.{0} := veblen 2 (gcG 0 + 1 + L.l)

theorem B_lt {μ : Ordinal.{0}} (h : μ < L.l) : (L.F μ).B < L.BU := by
  rw [L.H.B μ h]; exact ha_Q_lt_Q h

theorem B_cof {c : Ordinal.{0}} (hc : c < L.BU) : ∃ μ, μ < L.l ∧ c < (L.F μ).B := by
  have hlim : IsSuccLimit (gcG 0 + 1 + L.l) := isSuccLimit_add _ L.l_lim
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 2).lt_iff_exists_lt hlim).1 hc
  obtain ⟨d, hd, htd⟩ := (lt_add_iff L.l_lim.bot_lt.ne').1 ht
  exact ⟨d, hd, by rw [L.H.B d hd]; exact hct.trans_le ((isNormal_veblen 2).monotone htd)⟩

/-- The first member containing `c`. -/
noncomputable def N (c : Ordinal.{0}) : Ordinal.{0} := sInf {μ | μ < L.l ∧ c < (L.F μ).B}

theorem N_spec {c ν : Ordinal.{0}} (hν : ν < L.l) (hc : c < (L.F ν).B) :
    L.N c ≤ ν ∧ L.N c < L.l ∧ c < (L.F (L.N c)).B := by
  have hne : ({μ | μ < L.l ∧ c < (L.F μ).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

theorem N_min {c μ : Ordinal.{0}} (hμ : μ < L.N c) (hμl : μ < L.l) : ¬ c < (L.F μ).B := fun hcμ =>
  absurd (csInf_le' ⟨hμl, hcμ⟩ : L.N c ≤ μ) (not_le.2 hμ)

theorem N_high {c : Ordinal.{0}} (hc : L.BU ≤ c) : L.N c = 0 := by
  unfold HaLFam.N
  have he : ({μ | μ < L.l ∧ c < (L.F μ).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (L.B_lt hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

/-- The reading of the union. -/
noncomputable def R (c x : Ordinal.{0}) : Ordinal.{0} := (L.F (L.N c)).R c x

/-- The gate of the union. -/
noncomputable def g (c : Ordinal.{0}) : Ordinal.{0} := (L.F (L.N c)).g c

theorem R_eq {c ν : Ordinal.{0}} (hν : ν < L.l) (hc : c < (L.F ν).B) (x : Ordinal.{0}) :
    L.R c x = (L.F ν).R c x := by
  obtain ⟨h1, -, h3⟩ := L.N_spec hν hc
  exact (L.H.cohR _ _ h1 hν c x h3).symm

theorem g_eq {c ν : Ordinal.{0}} (hν : ν < L.l) (hc : c < (L.F ν).B) : L.g c = (L.F ν).g c := by
  obtain ⟨h1, -, h3⟩ := L.N_spec hν hc
  exact (L.H.cohg _ _ h1 hν c h3).symm

theorem BU_E : InE L.BU := gg_veblen_eps two_ne_zero

theorem BU_lim : IsSuccLimit L.BU := ev_isSuccLimit_of_inE L.BU_E

theorem R_succ' (c x : Ordinal.{0}) : L.R (c + 1) x = L.R c x + 1 := by
  rcases lt_or_ge c L.BU with h | h
  · obtain ⟨n, hn1, hn⟩ := L.B_cof (L.BU_lim.add_one_lt h)
    rw [L.R_eq hn1 hn, L.R_eq hn1 ((lt_add_one c).trans hn), (L.F n).R_succ]
  · unfold HaLFam.R
    rw [L.N_high h, L.N_high (h.trans (le_self_add (a := c) (b := 1))), (L.F 0).R_succ]

theorem g_le_succ' (c : Ordinal.{0}) : L.g c ≤ L.g (c + 1) := by
  rcases lt_or_ge c L.BU with h | h
  · obtain ⟨n, hn1, hn⟩ := L.B_cof (L.BU_lim.add_one_lt h)
    rw [L.g_eq hn1 hn, L.g_eq hn1 ((lt_add_one c).trans hn)]; exact (L.F n).g_le_succ c
  · unfold HaLFam.g
    rw [L.N_high h, L.N_high (h.trans (le_self_add (a := c) (b := 1)))]; exact (L.F 0).g_le_succ c

theorem l_pos : 0 < L.l := L.l_lim.bot_lt

theorem self_lt {μ : Ordinal.{0}} (h : μ < L.l) : μ < (L.F μ).B := L.H.self_lt h (L.lt_T h)

/-- **The index `λ` lies in an earlier start.** -/
theorem idx_spec : L.N L.l < L.l ∧ L.l < (L.F (L.N L.l)).B := by
  obtain ⟨μ, hμ, hlμ⟩ := ha_cover L.l_lim L.l_lt
  obtain ⟨-, h2, h3⟩ := L.N_spec hμ (by rw [L.H.B μ hμ]; exact hlμ)
  exact ⟨h2, h3⟩

/-- The system reading the index `λ`: the first start containing it. -/
noncomputable def E : GzVD := L.F (L.N L.l)

theorem idx_lt : L.l < L.E.B := L.idx_spec.2

/-- **The stage at `λ`**, read by `E`. -/
noncomputable def Bp : HaPB := haPBof L.E L.l L.idx_lt (ha_j L.l_lt)

theorem Bp_Q : L.Bp.Q = L.BU := rfl

theorem Bp_γ : L.Bp.γP = L.E.g L.l := rfl

theorem Bp_P {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : L.E.g L.l < x) :
    L.Bp.P x = veblen 2 (gzI0 x + L.E.R L.l x) := haPBof_P _ _ _ _ hx hx1 hγ

theorem E_R {μ : Ordinal.{0}} (h : μ < L.l) (x : Ordinal.{0}) : L.E.R μ x = (L.F μ).R μ x :=
  L.H.R_tr h L.idx_spec.1 (h.trans L.idx_lt) (L.self_lt h) x

theorem E_g {μ : Ordinal.{0}} (h : μ < L.l) : L.E.g μ = (L.F μ).g μ :=
  L.H.g_tr h L.idx_spec.1 (h.trans L.idx_lt) (L.self_lt h)

theorem st {μ : Ordinal.{0}} (h : μ < L.l) : HaSStart (haPBof (L.F μ) μ (L.self_lt h) (ha_j (L.lt_T h))) (L.F μ) :=
  L.H.st μ (L.lt_T h) h (L.self_lt h)

/-- **The base gate of the start `μ` lies below a base `x` iff the gate of `μ` does.** -/
theorem γ_iff {μ x : Ordinal.{0}} (h : μ < L.l) (hx : InE x) (hx1 : x < Om1) :
    (L.F μ).γ < x ↔ L.E.g μ < x := by
  rw [L.E_g h]; exact (L.st h).γ x hx hx1

/-- **The base reading of the start `μ` is `P_μ(x) = φ(2, i₀(x) + μ(x))`** above its gate. -/
theorem b_eq {μ x : Ordinal.{0}} (h : μ < L.l) (hx : InE x) (hx1 : x < Om1) (hγ : (L.F μ).γ < x) :
    (L.F μ).b x = veblen 2 (gzI0 x + L.E.R μ x) := by
  have hg : (L.F μ).g μ < x := (L.st h).γ x hx hx1 |>.1 hγ
  rw [(L.st h).b x hx hx1 hg, haPBof_P _ _ _ _ hx hx1 hg, L.E_R h]

theorem l_read_lim {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγx : L.E.g L.l < x) :
    IsSuccLimit (L.E.R L.l x) := by
  obtain ⟨cp, lp, T, -, -, hdec, -⟩ := L.E.ld L.l L.l_lim L.idx_lt
  obtain ⟨e, -, hT, -⟩ := hdec x hx hx1 hγx
  rw [e]
  exact isSuccLimit_add _ (isSuccLimit_opow_left isSuccLimit_omega0 hT)

theorem P_lt {μ x : Ordinal.{0}} (h : μ < L.l) (hx : InE x) (hx1 : x < Om1) (hγx : L.E.g L.l < x)
    (hμ : L.E.g μ < x) : veblen 2 (gzI0 x + L.E.R μ x) < L.Bp.P x := by
  rw [L.Bp_P hx hx1 hγx]
  exact (isNormal_veblen 2).strictMono ((add_lt_add_iff_left _).2 (L.E.mono x hx hx1 L.l L.idx_lt μ h hγx hμ))

/-- **`b_μ(x) < P_λ(x)`** for every start `μ < λ` with base gate below `x`. -/
theorem b_le {μ x : Ordinal.{0}} (h : μ < L.l) (hx : InE x) (hx1 : x < Om1) (hγx : L.E.g L.l < x)
    (hγ : (L.F μ).γ < x) : (L.F μ).b x ≤ L.Bp.P x := by
  rw [L.b_eq h hx hx1 hγ]
  exact (L.P_lt h hx hx1 hγx ((L.γ_iff h hx hx1).1 hγ)).le

/-- **The bound fields grow**: `Zst_μ(x) ≤ Zst_λ(x)` for every start `μ < λ` with base gate below `x`. -/
theorem Z_le {μ x : Ordinal.{0}} (h : μ < L.l) (hx : InE x) (hx1 : x < Om1) (hγ : (L.F μ).γ < x) :
    (L.F μ).Z x ≤ L.Bp.Zst x := by
  have hg : (L.F μ).g μ < x := (L.st h).γ x hx hx1 |>.1 hγ
  rw [(L.st h).Z x hx hx1]
  set Bμ := haPBof (L.F μ) μ (L.self_lt h) (ha_j (L.lt_T h)) with hBμ
  have hgμ : Bμ.γP < x := hg
  rw [Bμ.Zst_eq hgμ]
  by_cases hl : L.E.g L.l < x
  · rw [L.Bp.Zst_eq hl]
    have hP : Bμ.P x = veblen 2 (gzI0 x + L.E.R μ x) := by
      rw [haPBof_P _ _ _ _ hx hx1 hg, L.E_R h]
    have h1 : Bμ.P x < L.Bp.P x := by rw [hP]; exact L.P_lt h hx hx1 hl (by rw [L.E_g h]; exact hg)
    have h2 : evZ (Bμ.P x) ≤ L.Bp.P x := evZ_le h1 (L.Bp.P_fix hx hx1 hl)
    exact h2.trans (lt_evZ _).le
  · rw [L.Bp.Zst_low hl]
    exact (Bμ.evP_B3 hx hx1 hgμ).le

/-- **A code of the union with gate below a base `σ` lies in a start with base gate below `σ`.** -/
theorem small {c σ : Ordinal.{0}} (hc : c < L.BU) (hσ : InE σ) (hσ1 : σ < Om1) (hg : L.g c < σ) :
    ∃ μ, μ < L.l ∧ c < (L.F μ).B ∧ (L.F μ).γ < σ := by
  obtain ⟨n, hn1, hn⟩ := L.B_cof hc
  obtain ⟨-, hN1, hcN⟩ := L.N_spec hn1 hn
  have hgN : L.g c = (L.F (L.N c)).g c := rfl
  rcases zero_or_succ_or_isSuccLimit (L.N c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨L.N c, hN1, hcN, ?_⟩
    rw [L.γ_iff hN1 hσ hσ1, h0]
    have : L.E.g 0 = 0 := L.E.g_zero
    rw [this]; exact hσ.pos
  · have hm' : L.N c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < L.N c := by rw [hm']; exact lt_add_one m
    have hml : m < L.l := hmN.trans hN1
    have hBc : (L.F m).B ≤ c := not_lt.1 (L.N_min hmN hml)
    refine ⟨L.N c, hN1, hcN, ?_⟩
    rw [hgN, hm'] at hg
    rw [hm'] at hcN ⊢
    exact L.H.high m (hm' ▸ hN1) c σ hBc hcN hσ hσ1 hg
  · exfalso
    rw [L.H.B _ hN1] at hcN
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 2).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hcN
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < L.l := hd.trans hN1
    refine L.N_min hd hdl ?_
    rw [L.H.B d hdl]; exact hct.trans_le ((isNormal_veblen 2).monotone htd)

/-- **THE UNION AT A LIMIT `ζ`-INDEX `λ`**: bound `Q_λ`, base gate `g(λ)`, base reading `P_λ(x)`, bound field
`Zst_λ`. -/
noncomputable def U : GzVD where
  B := L.BU
  γ := L.E.g L.l
  γ_lt := L.E.g_lt L.l L.idx_lt
  γ_cl := fun _ hZ hZ1 h => L.Bp.Q_gate hZ hZ1 h
  γ_G := fun h => absurd h (ha_G_lt_Q L.l).ne'
  R := L.R
  g := L.g
  b := L.Bp.P
  ba := L.Bp.P
  ix := L.Bp.Q
  Z := L.Bp.Zst
  B_E := L.BU_E
  G_le := L.Bp.G_le_Q
  B_lt1 := L.Bp.Q_lt_G1
  B_ix := L.Bp.Q_fix.symm
  Z_fix := fun x _ _ => L.Bp.Zst_fix x
  Z_B3 := L.Bp.Zst_B3
  ix_mem := fun S a b ha hb => L.Bp.Q_mem S ha hb
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    rw [L.g_eq hn1 hn]; exact (L.F n).g_lt c hn
  g_zero := by rw [L.g_eq L.l_pos (L.F 0).B_pos]; exact (L.F 0).g_zero
  g_nat := fun k => by rw [L.g_eq L.l_pos ((L.F 0).nat_lt_B k)]; exact (L.F 0).g_nat k
  g_E := by rw [L.g_eq L.l_pos (L.F 0).E_lt_B]; exact (L.F 0).g_E
  g_lowE := fun c hc => by rw [L.g_eq L.l_pos (hc.trans (L.F 0).E_lt_B)]; exact (L.F 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof h
    rw [L.g_eq hn1 hn]; exact (L.F n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hxy
    have hx : x < (L.F n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (L.F n).B := lt_of_le_of_lt le_add_self hn
    rw [L.g_eq hn1 hn]; rw [L.g_eq hn1 hx] at hgx; rw [L.g_eq hn1 hy] at hgy
    exact (L.F n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hy
    have hy' : y < (L.F n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    rw [L.g_eq hn1 hn]; rw [L.g_eq hn1 hy'] at hg
    exact (L.F n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hcB
    rw [L.g_eq hn1 hn]
    exact (L.F n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (L.B_lt hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    have hc' : c < (L.F n).B := (lt_add_one c).trans hn
    rw [L.g_eq hn1 hn]; rw [L.g_eq hn1 hc'] at hg
    exact (L.F n).g_succ Z hZ c hn hg
  g_le_succ := L.g_le_succ'
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    rw [L.g_eq hn1 hn] at hg
    exact (L.F n).mem S a b ha c hn hg
  R_zero := fun x => by rw [L.R_eq L.l_pos (L.F 0).B_pos]; exact (L.F 0).R_zero x
  R_nat := fun k x => by rw [L.R_eq L.l_pos ((L.F 0).nat_lt_B k)]; exact (L.F 0).R_nat k x
  R_E := fun x => by rw [L.R_eq L.l_pos (L.F 0).E_lt_B]; exact (L.F 0).R_E x
  R_succ := L.R_succ'
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    rw [L.R_eq hn1 hn]; rw [L.g_eq hn1 hn] at hg
    exact (L.F n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    rw [L.R_eq hn1 hn]; rw [L.g_eq hn1 hn] at hg
    exact (L.F n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 hγx c hc hg => by
    obtain ⟨μ, hμ, hcμ, hγμ⟩ := L.small hc hx hx1 hg
    rw [L.R_eq hμ hcμ]; rw [L.g_eq hμ hcμ] at hg
    exact ((L.F μ).R_lt_b x hx hx1 hγμ c hcμ hg).trans_le (L.b_le hμ hx hx1 hγx hγμ)
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨μ, hμ, hcμ, hγμ⟩ := L.small hc hx hx1 hg
    rw [L.R_eq hμ hcμ]; rw [L.g_eq hμ hcμ] at hg
    exact ((L.F μ).R_lt_Z x hx hx1 c hcμ hg).trans_le (L.Z_le hμ hx hx1 hγμ)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    have hd : d < (L.F n).B := hdc.trans hn
    rw [L.R_eq hn1 hn, L.R_eq hn1 hd]; rw [L.g_eq hn1 hn] at hgc; rw [L.g_eq hn1 hd] at hgd
    exact (L.F n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    rw [L.R_eq hn1 hn] at hν; rw [L.g_eq hn1 hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (L.F n).cof x hx hx1 c hn hg ν hν
    have hd : d < (L.F n).B := hdc.trans hn
    exact ⟨d, hdc, by rw [L.g_eq hn1 hd]; exact hgd, by rw [L.R_eq hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 hγx ν hν => by
    rw [L.Bp_P hx hx1 hγx] at hν
    have hRl := L.l_read_lim hx hx1 hγx
    have hlim : IsSuccLimit (gzI0 x + L.E.R L.l x) := isSuccLimit_add _ hRl
    obtain ⟨t, ht, hνt⟩ := ((isNormal_veblen 2).lt_iff_exists_lt hlim).1 hν
    obtain ⟨d0, hd0, htd⟩ := (lt_add_iff hRl.bot_lt.ne').1 ht
    obtain ⟨e, hel, hge, hd0e⟩ := L.E.cof x hx hx1 L.l L.idx_lt hγx d0 hd0
    have hγe : (L.F e).γ < x := (L.γ_iff hel hx hx1).2 hge
    have hb : ν < (L.F e).b x := by
      rw [L.b_eq hel hx hx1 hγe]
      exact hνt.trans_le ((isNormal_veblen 2).monotone (htd.trans ((add_le_add_iff_left _).2 hd0e)))
    obtain ⟨c, hc, hgc, hνc⟩ := (L.F e).b_cof x hx hx1 hγe ν hb
    exact ⟨c, hc.trans (L.B_lt hel), by rw [L.g_eq hel hc]; exact hgc, by rw [L.R_eq hel hc]; exact hνc⟩
  b_E := fun x hx hx1 hγ => (L.Bp.P_facts hx hx1 hγ).2.2.2
  x_lt_b := fun x hx hx1 hγ => L.Bp.P_gt hx hx1 hγ
  b_eN := fun x hx hx1 hγ => gz_eN_fix hx hx1 (L.Bp.P_fix hx hx1 hγ) (L.Bp.P_gt hx hx1 hγ) (L.Bp.P_lt hx hx1 hγ)
  ba_lt := fun x hx hx1 hγ => L.Bp.P_lt hx hx1 hγ
  b_Z := fun x _ _ hγ => by
    show _ < L.Bp.Zst x
    rw [L.Bp.Zst_eq hγ]; exact go_eN_lt_evZ (lt_evZ _)
  b_pi := fun _ _ hB hγ => L.Bp.P_pi hB hγ
  ba_pi := fun _ _ hB hγ => L.Bp.P_pi hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    rw [L.R_eq hn1 hn, L.R_eq hn1 hn]; rw [L.g_eq hn1 hn] at hg
    exact (L.F n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB hγσ d hd hg P P' hat => by
    obtain ⟨μ, hμ, hdμ, hγμ⟩ := L.small hd hB.1 (hB.2.2.1.trans hB.2.2.2) hg
    rw [L.R_eq hμ hdμ, L.R_eq hμ hdμ]; rw [L.g_eq hμ hdμ] at hg
    exact (L.F μ).dig σ ρ hB hγμ d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans_le (L.b_le hμ hB.2.1 hB.2.2.2 (hγσ.trans hB.2.2.1) (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (L.F n).ld c hl hn
    have hcpn : cp < (L.F n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [L.g_eq hn1 hn, L.g_eq hn1 hcpn]; exact hgcp, fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← L.g_eq hn1 hn]; exact hg)⟩
    rw [L.g_eq hn1 hn] at hg
    rw [L.R_eq hn1 hn, L.R_eq hn1 hcpn]
    exact hdec x hx hx1 hg

theorem U_R {ν c : Ordinal.{0}} (hν : ν < L.l) (hc : c < (L.F ν).B) (x : Ordinal.{0}) :
    L.U.R c x = (L.F ν).R c x := L.R_eq hν hc x

theorem U_g {ν c : Ordinal.{0}} (hν : ν < L.l) (hc : c < (L.F ν).B) : L.U.g c = (L.F ν).g c := L.g_eq hν hc

theorem U_B : L.U.B = veblen 2 (gcG 0 + 1 + L.l) := rfl

theorem U_self : L.l < L.U.B := ha_lt_Q L.l_lt

/-- **THE UNION AT THE LIMIT `ζ`-INDEX `λ` STARTS THE STAGE `λ`** (with `λ` read by the union itself). -/
theorem U_start : HaSStart (haPBof L.U L.l L.U_self (ha_j L.l_lt)) L.U where
  ix := rfl
  γ := fun _ _ _ => Iff.rfl
  b := fun _ _ _ _ => rfl
  Z := fun _ _ _ => rfl

end HaLFam

end Googology.Trans.PoR.InaccPsi.R2.Ha
