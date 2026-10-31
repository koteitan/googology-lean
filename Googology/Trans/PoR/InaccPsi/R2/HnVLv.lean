import Googology.Trans.PoR.InaccPsi.R2.HnVQ

/-!
# HnVLv (port of HlVLv): THE OFFSETS OVER A BASE OF THE GATED LEVEL `L + ν`: THE INVARIANT AND THE UNION AT A LIMIT

PORT of `Hl.HlVLv` (the same proofs) to the band level datum `Hn.HnLv`.  What differs from `Hl.HlLv`: a level is
`L = Ω₁·u + Ω₁·q` (`q < Ω₁`, any `u`) in place of `L = Ω₁·q`; the code gate `g < Z` is asked for codes in
`[L, Ω₁·u + Ω₁²)` in place of `[L, Ω₁²)`; there is no field `ℓ(x) + x < x·x` (it is a hypothesis of the base `G`
only).  Declarations that do not mention a level datum are imported from `Hl`, not copied.

PORT of `Hj.HjVLv`.

What differs from the source: the level datum is a GATED one (`Hl.HlLv`: Lemma EXACT for the reading `ℓ` only at
base pairs `(σ, ρ)` above the level gate `g`, the hull membership of `L` only at `0 < a`, `g < b`, the code gate
`g < Z` only when a code over `Z` exists at the level); every pseudo-base and base carries `g ≤` its reading gate
(fields `lg`), and the code-gate fields take the extra hypothesis `g < Z`.  Proofs are otherwise those of the source;
names: prefix `hl`/`Hl` in place of `hj`/`Hj`.

No new axiom.  New definitions: `hnVMPB`, `HnVInv`, `HnVFam`, `HnVFam.BU`, `HnVFam.N`, `HnVFam.R`, `HnVFam.g`,
`HnVFam.E`, `HnVFam.Bp`, `HnVFam.U`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hn

open Googology.Trans.PoR.InaccPsi.R2.Hl

open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk

open Googology.Trans.PoR.InaccPsi.R2.Hi

open Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

variable {Λ : HnLv}

/-! ## Helpers over a base -/

namespace HnVB

variable {κ : Ordinal.{0}} (A : HnVB Λ κ)

theorem lvR_lt_N (E : HgVD) (hZ : ∀ x, InE x → x < Om1 → E.Z x ≤ A.Zl x) {c x : Ordinal.{0}} (hc : c < E.B)
    (hx : InE x) (hx1 : x < Om1) (hγ : A.γN < x) (hg : E.g c < x) : E.R c x < hcN (Λ.l x + κ) (A.Fr x) := by
  have h := (E.R_lt_Z x hx hx1 c hc hg).trans_le (hZ x hx hx1)
  rwa [A.Zl_eq hx hγ] at h

theorem lvt_lt (E : HgVD) (hZ : ∀ x, InE x → x < Om1 → E.Z x ≤ A.Zl x) {c x : Ordinal.{0}} (hc : c < E.B)
    (hx : InE x) (hx1 : x < Om1) (hγ : A.γN < x) (hg : E.g c < x) : A.Fr x + E.R c x < gq 1 x :=
  (inE_indec (gm1_facts hx hx1).2.2.2).add_lt (A.Fr_lt1 hx hx1 hγ)
    ((A.lvR_lt_N E hZ hc hx hx1 hγ hg).trans (A.N_lt1x hx hx1 hγ))

end HnVB

/-- The stage at the offset `λ` over `A`, `λ` read by `E`. -/
noncomputable abbrev hnVMPB {κ : Ordinal.{0}} (A : HnVB Λ κ) (E : HgVD) (l : Ordinal.{0}) (hlB : l < E.B)
    (hlN : l < hcN (Λ.L + κ) A.F) (hZ : ∀ x, InE x → x < Om1 → E.Z x ≤ A.Zl x) : HgPB :=
  hnVPB (hnVOff A E l hlB hlN hZ)

/-! ## The invariant -/

/-- **The invariant of the starts below `λ` over the pseudo-base `A`.** -/
structure HnVInv {κ : Ordinal.{0}} (A : HnVB Λ κ) (l : Ordinal.{0}) (F : Ordinal.{0} → HgVD) : Prop where
  B : ∀ μ, μ < l → (F μ).B = veblen (Λ.L + κ) (A.F + 1 + μ)
  Zb : ∀ μ, μ < l → ∀ x, InE x → x < Om1 → (F μ).Z x ≤ A.Zl x
  st : ∀ μ (hμ : μ < hcN (Λ.L + κ) A.F), μ < l → ∀ (h2 : μ < (F μ).B) (hZ : ∀ x, InE x → x < Om1 →
      (F μ).Z x ≤ A.Zl x),
    HgSStart (hnVMPB A (F μ) μ h2 hμ hZ) (F μ)
  high : ∀ μ, μ + 1 < l → ∀ c σ, (F μ).B ≤ c → c < (F (μ + 1)).B → InE σ → σ < Om1 →
    (F (μ + 1)).g c < σ → (F (μ + 1)).γ < σ
  cohR : ∀ β γ, β ≤ γ → γ < l → ∀ c x, c < (F β).B → (F γ).R c x = (F β).R c x
  cohg : ∀ β γ, β ≤ γ → γ < l → ∀ c, c < (F β).B → (F γ).g c = (F β).g c

theorem hnV_st_congr {κ : Ordinal.{0}} {A : HnVB Λ κ} {D D' : HgVD} (e : D = D') {μ : Ordinal.{0}} (h2 : μ < D.B) (hμ :
    μ < hcN (Λ.L + κ) A.F)
    (hZ : ∀ x, InE x → x < Om1 → D.Z x ≤ A.Zl x)
    (h : ∀ (h2' : μ < D'.B) (hZ' : ∀ x, InE x → x < Om1 → D'.Z x ≤ A.Zl x),
      HgSStart (hnVMPB A D' μ h2' hμ hZ') D') : HgSStart (hnVMPB A D μ h2 hμ hZ) D := by
  subst e; exact h h2 hZ

namespace HnVInv

variable {κ : Ordinal.{0}} {A : HnVB Λ κ} {l : Ordinal.{0}} {F : Ordinal.{0} → HgVD} (H : HnVInv A l F)
include H

theorem self_lt {μ : Ordinal.{0}} (h : μ < l) (hT : μ < hcN (Λ.L + κ) A.F) : μ < (F μ).B := by
  rw [H.B μ h]; exact A.lt_Q hT

theorem R_tr {μ d : Ordinal.{0}} (hμ : μ < l) (hf : d < l) (hμd : μ < (F d).B) (hμB : μ < (F μ).B)
    (x : Ordinal.{0}) : (F d).R μ x = (F μ).R μ x := by
  rcases le_total μ d with h | h
  · exact H.cohR μ d h hf μ x hμB
  · exact (H.cohR d μ h hμ μ x hμd).symm

theorem g_tr {μ d : Ordinal.{0}} (hμ : μ < l) (hf : d < l) (hμd : μ < (F d).B) (hμB : μ < (F μ).B) :
    (F d).g μ = (F μ).g μ := by
  rcases le_total μ d with h | h
  · exact H.cohg μ d h hf μ hμB
  · exact (H.cohg d μ h hμ μ hμd).symm

theorem congr {G : Ordinal.{0} → HgVD} (hFG : ∀ β, β < l → G β = F β) : HnVInv A l G where
  B := fun μ h => by rw [hFG μ h]; exact H.B μ h
  Zb := fun μ h => by rw [hFG μ h]; exact H.Zb μ h
  st := fun μ hμ h h2 hZ => hnV_st_congr (hFG μ h) h2 hμ hZ (H.st μ hμ h)
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

end HnVInv

/-! ## The union at a limit offset -/

/-- **The family of all starts below a limit offset `λ < N(F)`.** -/
structure HnVFam {κ : Ordinal.{0}} (A : HnVB Λ κ) where
  l : Ordinal.{0}
  F : Ordinal.{0} → HgVD
  l_lim : IsSuccLimit l
  l_lt : l < hcN (Λ.L + κ) A.F
  I : HnVInv A l F

namespace HnVFam

variable {κ : Ordinal.{0}} {A : HnVB Λ κ} (L : HnVFam A)

theorem lt_N {μ : Ordinal.{0}} (h : μ < L.l) : μ < hcN (Λ.L + κ) A.F := h.trans L.l_lt

/-- The bound of the union, `Q_λ = φ(2, F + 1 + λ)`. -/
noncomputable def BU : Ordinal.{0} := veblen (Λ.L + κ) (A.F + 1 + L.l)

theorem B_lt {μ : Ordinal.{0}} (h : μ < L.l) : (L.F μ).B < L.BU := by
  rw [L.I.B μ h]; exact A.Q_lt_Q h

theorem B_cof {c : Ordinal.{0}} (hc : c < L.BU) : ∃ μ, μ < L.l ∧ c < (L.F μ).B := by
  have hlim : IsSuccLimit (A.F + 1 + L.l) := isSuccLimit_add _ L.l_lim
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen (Λ.L + κ)).lt_iff_exists_lt hlim).1 hc
  obtain ⟨d, hf, htd⟩ := (lt_add_iff L.l_lim.bot_lt.ne').1 ht
  exact ⟨d, hf, by rw [L.I.B d hf]; exact hct.trans_le ((isNormal_veblen (Λ.L + κ)).monotone htd)⟩

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
  unfold HnVFam.N
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
  exact (L.I.cohR _ _ h1 hν c x h3).symm

theorem g_eq {c ν : Ordinal.{0}} (hν : ν < L.l) (hc : c < (L.F ν).B) : L.g c = (L.F ν).g c := by
  obtain ⟨h1, -, h3⟩ := L.N_spec hν hc
  exact (L.I.cohg _ _ h1 hν c h3).symm

theorem BU_E : InE L.BU := gg_veblen_eps (hnv_L0 Λ κ)

theorem BU_lim : IsSuccLimit L.BU := ev_isSuccLimit_of_inE L.BU_E

theorem R_succ' (c x : Ordinal.{0}) : L.R (c + 1) x = L.R c x + 1 := by
  rcases lt_or_ge c L.BU with h | h
  · obtain ⟨n, hn1, hn⟩ := L.B_cof (L.BU_lim.add_one_lt h)
    rw [L.R_eq hn1 hn, L.R_eq hn1 ((lt_add_one c).trans hn), (L.F n).R_succ]
  · unfold HnVFam.R
    rw [L.N_high h, L.N_high (h.trans (le_self_add (a := c) (b := 1))), (L.F 0).R_succ]

theorem g_le_succ' (c : Ordinal.{0}) : L.g c ≤ L.g (c + 1) := by
  rcases lt_or_ge c L.BU with h | h
  · obtain ⟨n, hn1, hn⟩ := L.B_cof (L.BU_lim.add_one_lt h)
    rw [L.g_eq hn1 hn, L.g_eq hn1 ((lt_add_one c).trans hn)]; exact (L.F n).g_le_succ c
  · unfold HnVFam.g
    rw [L.N_high h, L.N_high (h.trans (le_self_add (a := c) (b := 1)))]; exact (L.F 0).g_le_succ c

theorem l_pos : 0 < L.l := L.l_lim.bot_lt

theorem self_lt {μ : Ordinal.{0}} (h : μ < L.l) : μ < (L.F μ).B := L.I.self_lt h (L.lt_N h)

/-- **The index `λ` lies in an earlier start.** -/
theorem idx_spec : L.N L.l < L.l ∧ L.l < (L.F (L.N L.l)).B := by
  obtain ⟨μ, hμ, hlμ⟩ := A.cover L.l_lim L.l_lt
  obtain ⟨-, h2, h3⟩ := L.N_spec hμ (by rw [L.I.B μ hμ]; exact hlμ)
  exact ⟨h2, h3⟩

/-- The system reading the index `λ`: the first start containing it. -/
noncomputable def E : HgVD := L.F (L.N L.l)

theorem idx_lt : L.l < L.E.B := L.idx_spec.2

theorem E_Zb : ∀ x, InE x → x < Om1 → L.E.Z x ≤ A.Zl x := L.I.Zb _ L.idx_spec.1

/-- **The stage at `λ`**, read by `E`. -/
noncomputable def Bp : HgPB := hnVMPB A L.E L.l L.idx_lt L.l_lt L.E_Zb

theorem Bp_Q : L.Bp.Q = L.BU := rfl

theorem Bp_γ : L.Bp.γP = max A.γN (L.E.g L.l) := rfl

theorem Bp_P (x : Ordinal.{0}) : L.Bp.P x = glA (Λ.l x + κ) (A.Fr x + L.E.R L.l x) x := rfl

theorem E_R {μ : Ordinal.{0}} (h : μ < L.l) (x : Ordinal.{0}) : L.E.R μ x = (L.F μ).R μ x :=
  L.I.R_tr h L.idx_spec.1 (h.trans L.idx_lt) (L.self_lt h) x

theorem E_g {μ : Ordinal.{0}} (h : μ < L.l) : L.E.g μ = (L.F μ).g μ :=
  L.I.g_tr h L.idx_spec.1 (h.trans L.idx_lt) (L.self_lt h)

theorem st {μ : Ordinal.{0}} (h : μ < L.l) :
    HgSStart (hnVMPB A (L.F μ) μ (L.self_lt h) (L.lt_N h) (L.I.Zb μ h)) (L.F μ) :=
  L.I.st μ (L.lt_N h) h (L.self_lt h) (L.I.Zb μ h)

/-- **The base gate of the start `μ` lies below a base `x` iff `max(γ_F, g(μ))` does.** -/
theorem γ_iff {μ x : Ordinal.{0}} (h : μ < L.l) (hx : InE x) (hx1 : x < Om1) :
    (L.F μ).γ < x ↔ max A.γN (L.E.g μ) < x := by
  rw [L.E_g h]; exact (L.st h).γ x hx hx1

/-- **The base reading of the start `μ` is `ϑˣ(Ω₁·2 + F(x) + μ(x))`** above its gate. -/
theorem b_eq {μ x : Ordinal.{0}} (h : μ < L.l) (hx : InE x) (hx1 : x < Om1) (hγ : (L.F μ).γ < x) :
    (L.F μ).b x = glA (Λ.l x + κ) (A.Fr x + L.E.R μ x) x := by
  have hg : max A.γN ((L.F μ).g μ) < x := (L.st h).γ x hx hx1 |>.1 hγ
  rw [(L.st h).b x hx hx1 hg, L.E_R h]; rfl

theorem l_read_lim {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγx : L.E.g L.l < x) :
    IsSuccLimit (L.E.R L.l x) := by
  obtain ⟨cp, lp, T, -, -, hfec, -⟩ := L.E.ld L.l L.l_lim L.idx_lt
  obtain ⟨e, -, hT, -⟩ := hfec x hx hx1 hγx
  rw [e]
  exact isSuccLimit_add _ (isSuccLimit_opow_left isSuccLimit_omega0 hT)

theorem P_lt {μ x : Ordinal.{0}} (h : μ < L.l) (hx : InE x) (hx1 : x < Om1) (hγx : max A.γN (L.E.g L.l) < x)
    (hμ : L.E.g μ < x) : glA (Λ.l x + κ) (A.Fr x + L.E.R μ x) x < L.Bp.P x := by
  have hA : A.γN < x := (max_lt_iff.1 hγx).1
  have hl : L.E.g L.l < x := (max_lt_iff.1 hγx).2
  have hμB : μ < L.E.B := h.trans L.idx_lt
  obtain ⟨h2T, h21⟩ := hnv_T Λ hx hx1 (A.ν_lt hx hx1 hA)
  obtain ⟨hμT, -⟩ := gm1_T hx hx1 (A.lvt_lt L.E L.E_Zb hμB hx hx1 hA hμ)
  obtain ⟨hlT, hl1⟩ := gm1_T hx hx1 (A.lvt_lt L.E L.E_Zb L.idx_lt hx hx1 hA hl)
  exact glA_lt_of hx hx1 (hnv_one Λ hx hx1 (A.ν_lt hx hx1 hA)) h2T h21 hμT hlT hl1
    ((add_lt_add_iff_left _).2 (L.E.mono x hx hx1 L.l L.idx_lt μ h hl hμ))

/-- **`b_μ(x) < P_λ(x)`** for every start `μ < λ` with base gate below `x`. -/
theorem b_le {μ x : Ordinal.{0}} (h : μ < L.l) (hx : InE x) (hx1 : x < Om1) (hγx : max A.γN (L.E.g L.l) < x)
    (hγ : (L.F μ).γ < x) : (L.F μ).b x ≤ L.Bp.P x := by
  rw [L.b_eq h hx hx1 hγ]
  exact (L.P_lt h hx hx1 hγx (max_lt_iff.1 ((L.γ_iff h hx hx1).1 hγ)).2).le

/-- **The bound fields grow**: `Zst_μ(x) ≤ Zst_λ(x)` for every start `μ < λ` with base gate below `x`. -/
theorem Z_le {μ x : Ordinal.{0}} (h : μ < L.l) (hx : InE x) (hx1 : x < Om1) (hγ : (L.F μ).γ < x) :
    (L.F μ).Z x ≤ L.Bp.Zst x := by
  by_cases hl : max A.γN (L.E.g L.l) < x
  · have hg : max A.γN ((L.F μ).g μ) < x := (L.st h).γ x hx hx1 |>.1 hγ
    rw [(L.st h).Z x hx hx1, HgPB.Zst_eq _ hg, L.Bp.Zst_eq hl]
    have h1 : glA (Λ.l x + κ) (A.Fr x + (L.F μ).R μ x) x < L.Bp.P x := by
      rw [← L.E_R h]; exact L.P_lt h hx hx1 hl (by rw [L.E_g h]; exact (max_lt_iff.1 hg).2)
    exact (evZ_le h1 (L.Bp.P_fix hx hx1 hl)).trans (lt_evZ _).le
  · rw [L.Bp.Zst_low hl]; exact L.I.Zb μ h x hx hx1

/-- **A code of the union with gate below a base `σ > γ_F` lies in a start with base gate below `σ`.** -/
theorem small {c σ : Ordinal.{0}} (hc : c < L.BU) (hσ : InE σ) (hσ1 : σ < Om1) (hAσ : A.γN < σ) (hg : L.g c < σ) :
    ∃ μ, μ < L.l ∧ c < (L.F μ).B ∧ (L.F μ).γ < σ := by
  obtain ⟨n, hn1, hn⟩ := L.B_cof hc
  obtain ⟨-, hN1, hcN⟩ := L.N_spec hn1 hn
  have hgN : L.g c = (L.F (L.N c)).g c := rfl
  rcases zero_or_succ_or_isSuccLimit (L.N c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨L.N c, hN1, hcN, ?_⟩
    rw [L.γ_iff hN1 hσ hσ1, h0, L.E.g_zero, max_eq_left zero_le]
    exact hAσ
  · have hm' : L.N c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < L.N c := by rw [hm']; exact lt_add_one m
    have hml : m < L.l := hmN.trans hN1
    have hBc : (L.F m).B ≤ c := not_lt.1 (L.N_min hmN hml)
    refine ⟨L.N c, hN1, hcN, ?_⟩
    rw [hgN, hm'] at hg
    rw [hm'] at hcN ⊢
    exact L.I.high m (hm' ▸ hN1) c σ hBc hcN hσ hσ1 hg
  · exfalso
    rw [L.I.B _ hN1] at hcN
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen (Λ.L + κ)).lt_iff_exists_lt
        (isSuccLimit_add _ hlim)).1 hcN
    obtain ⟨d, hf, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hfl : d < L.l := hf.trans hN1
    refine L.N_min hf hfl ?_
    rw [L.I.B d hfl]; exact hct.trans_le ((isNormal_veblen (Λ.L + κ)).monotone htd)

/-- **THE UNION AT A LIMIT OFFSET `λ`**: bound `Q_λ`, base gate `max(γ_F, g(λ))`, base reading `P_λ(x)`, bound
field `Zst_λ`. -/
noncomputable def U : HgVD where
  B := L.BU
  γ := max A.γN (L.E.g L.l)
  γ_lt := L.Bp.γP_lt
  γ_cl := fun _ hZ hZ1 h => L.Bp.Q_gate hZ hZ1 h
  γ_G := fun h => absurd h (A.G_lt_Q L.l).ne'
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
  Z_G1 := L.Bp.Zst_G1
  ix_mem := fun S _ _ ha hb => L.Bp.Q_mem S ha hb
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
    obtain ⟨μ, hμ, hcμ, hγμ⟩ := L.small hc hx hx1 (max_lt_iff.1 hγx).1 hg
    rw [L.R_eq hμ hcμ]; rw [L.g_eq hμ hcμ] at hg
    exact ((L.F μ).R_lt_b x hx hx1 hγμ c hcμ hg).trans_le (L.b_le hμ hx hx1 hγx hγμ)
  R_lt_Z := fun x hx hx1 c hc hg => by
    by_cases hγx : max A.γN (L.E.g L.l) < x
    · obtain ⟨μ, hμ, hcμ, hγμ⟩ := L.small hc hx hx1 (max_lt_iff.1 hγx).1 hg
      rw [L.R_eq hμ hcμ]; rw [L.g_eq hμ hcμ] at hg
      exact ((L.F μ).R_lt_Z x hx hx1 c hcμ hg).trans_le (L.Z_le hμ hx hx1 hγμ)
    · obtain ⟨n, hn1, hn⟩ := L.B_cof hc
      rw [L.R_eq hn1 hn]; rw [L.g_eq hn1 hn] at hg
      show _ < L.Bp.Zst x
      rw [L.Bp.Zst_low hγx]
      exact ((L.F n).R_lt_Z x hx hx1 c hn hg).trans_le (L.I.Zb n hn1 x hx hx1)
  mono := fun x hx hx1 c hc d hfc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    have hf : d < (L.F n).B := hfc.trans hn
    rw [L.R_eq hn1 hn, L.R_eq hn1 hf]; rw [L.g_eq hn1 hn] at hgc; rw [L.g_eq hn1 hf] at hgd
    exact (L.F n).mono x hx hx1 c hn d hfc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    rw [L.R_eq hn1 hn] at hν; rw [L.g_eq hn1 hn] at hg
    obtain ⟨d, hfc, hgd, hνd⟩ := (L.F n).cof x hx hx1 c hn hg ν hν
    have hf : d < (L.F n).B := hfc.trans hn
    exact ⟨d, hfc, by rw [L.g_eq hn1 hf]; exact hgd, by rw [L.R_eq hn1 hf]; exact hνd⟩
  b_cof := fun x hx hx1 hγx ν hν => by
    have hA : A.γN < x := (max_lt_iff.1 hγx).1
    have hl : L.E.g L.l < x := (max_lt_iff.1 hγx).2
    obtain ⟨i0, hi0⟩ := hdNx_LuP (Λ.l x + κ) (A.Fr x)
    have hlN := A.lvR_lt_N L.E L.E_Zb L.idx_lt hx hx1 hA hl
    rw [L.Bp_P, A.lvglAV hx hx1 hA hi0 hlN] at hν
    have hRl := L.l_read_lim hx hx1 hl
    have hlim : IsSuccLimit (i0 + L.E.R L.l x) := isSuccLimit_add _ hRl
    obtain ⟨t, ht, hνt⟩ := ((isNormal_veblen (Λ.l x + κ)).lt_iff_exists_lt hlim).1 hν
    obtain ⟨d0, hf0, htd⟩ := (lt_add_iff hRl.bot_lt.ne').1 ht
    obtain ⟨e, hel, hge, hf0e⟩ := L.E.cof x hx hx1 L.l L.idx_lt hl d0 hf0
    have hγe : (L.F e).γ < x := (L.γ_iff hel hx hx1).2 (max_lt hA hge)
    have heN := A.lvR_lt_N L.E L.E_Zb (hel.trans L.idx_lt) hx hx1 hA hge
    have hb : ν < (L.F e).b x := by
      rw [L.b_eq hel hx hx1 hγe, A.lvglAV hx hx1 hA hi0 heN]
      exact hνt.trans_le ((isNormal_veblen (Λ.l x + κ)).monotone (htd.trans
          ((add_le_add_iff_left _).2 hf0e)))
    obtain ⟨c, hc, hgc, hνc⟩ := (L.F e).b_cof x hx hx1 hγe ν hb
    exact ⟨c, hc.trans (L.B_lt hel), by rw [L.g_eq hel hc]; exact hgc, by rw [L.R_eq hel hc]; exact hνc⟩
  b_E := fun x hx hx1 hγ => L.Bp.P_E hx hx1 hγ
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
  dig := fun σ ρ hB hγσ d hf hg P P' hat => by
    obtain ⟨μ, hμ, hfμ, hγμ⟩ := L.small hf hB.1 (hB.2.2.1.trans hB.2.2.2) (max_lt_iff.1 hγσ).1 hg
    rw [L.R_eq hμ hfμ, L.R_eq hμ hfμ]; rw [L.g_eq hμ hfμ] at hg
    exact (L.F μ).dig σ ρ hB hγμ d hfμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans_le (L.b_le hμ hB.2.1 hB.2.2.2 (hγσ.trans hB.2.2.1) (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := L.B_cof hc
    obtain ⟨cp, lp, T, hcp, hgcp, hfec, hex⟩ := (L.F n).ld c hl hn
    have hcpn : cp < (L.F n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [L.g_eq hn1 hn, L.g_eq hn1 hcpn]; exact hgcp, fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← L.g_eq hn1 hn]; exact hg)⟩
    rw [L.g_eq hn1 hn] at hg
    rw [L.R_eq hn1 hn, L.R_eq hn1 hcpn]
    exact hfec x hx hx1 hg

theorem U_R {ν c : Ordinal.{0}} (hν : ν < L.l) (hc : c < (L.F ν).B) (x : Ordinal.{0}) :
    L.U.R c x = (L.F ν).R c x := L.R_eq hν hc x

theorem U_g {ν c : Ordinal.{0}} (hν : ν < L.l) (hc : c < (L.F ν).B) : L.U.g c = (L.F ν).g c := L.g_eq hν hc

theorem U_B : L.U.B = veblen (Λ.L + κ) (A.F + 1 + L.l) := rfl

theorem U_self : L.l < L.U.B := A.lt_Q L.l_lt

theorem U_Zb : ∀ x, InE x → x < Om1 → L.U.Z x ≤ A.Zl x := fun x hx hx1 => L.Bp.Zst_le_Zl x hx hx1

/-- **THE UNION AT THE LIMIT OFFSET `λ` STARTS THE STAGE `λ`** (with `λ` read by the union itself). -/
theorem U_start : HgSStart (hnVMPB A L.U L.l L.U_self L.l_lt L.U_Zb) L.U where
  ix := rfl
  γ := fun _ _ _ => Iff.rfl
  b := fun _ _ _ _ => rfl
  Z := fun _ _ _ => rfl

end HnVFam

end Googology.Trans.PoR.InaccPsi.R2.Hn
