import Googology.Trans.PoR.InaccPsi.R2.HcGImg

/-!
# HcGInd: LEMMA IMG BELOW `φ(ω^ω, Γ_{ρ+1}+1)`, BY ONE TRANSFINITE INDUCTION ON THE VEBLEN LEVEL

`Hb.hb_DI` proves the reach test (`HbDown k`) and Lemma IMG over every pseudo-base (`HbNext k`) for every finite
level `k ≥ 2`, by induction on `k`.  Here the level `α` is an ordinal `2 ≤ α < ω^ω`, and ONE well-founded induction
on `α` passes every successor and every limit level by the same step (`hc_stepG`):

* over a fixed point `P` of `φ(α, ·)`, every ordinal in `(P, N_α(P))` is either a point `φ(α, P+1+d)` of level `α`
  (`= ϑᵖ(Ω₁·α + P + d)`, `Hc.hc_glAV`, reach `u·(1+α) + ζ`, `Hc.hc_lhG`) or lies in a gap `(φ(α, j), φ(α, j+1))`,
  which lies below `N_γ(φ(α, j))` for some `γ < α` (`Hc.hc_gap`), where the induction hypothesis at the level
  `max(γ, 2)` applies;
* at the points: Lemma IMG by the reach test going down (`Hc.hc_img_downG`), with `E'` the previous point at a
  successor `d`, and `E' = φ(α, P+1+c')`, `d = c' + ω^z`, at a limit `d` (the points between have
  `ζ ≤ logend < z`, `Hc.hc_zetaG`).

The finite levels come from `Hb.hb_DI`.  Then Lemma IMG holds below `N_α(Γ_{ρ+1})` for every `α < ω^ω`, hence below
`B_{ω^ω}(ρ) = φ(ω^ω, Γ_{ρ+1}+1)` (`hc_img_BW`), and Lemma IMG (gated) for a specified function below it
(`hc_pkg_BW`).

* `HcDownG`, `HcNextG`, `hc_gapDown`, `hc_gapNext`, `hc_step_cfG`, `hc_stepG` (**THE STEP, successor and limit
  levels alike**), `hc_DI` (**THE TRANSFINITE INDUCTION ON THE LEVEL**), `hc_img_lvl` (**LEMMA IMG BELOW
  `N_α(Γ_{ρ+1})`, EVERY `α < ω^ω`**), `hcBW`, `hcBW_lt1`, `hc_B1_lt_BW`, `hc_Bw_le_BW`, `hc_img_BW` (**LEMMA IMG BELOW
  `B_{ω^ω}(ρ)`**), `hc_pkg_BW`.

No new axiom.  New definitions: `HcDownG`, `HcNextG`, `hcBW`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hc

open Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gj Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gk
  Googology.Trans.PoR.InaccPsi.R2.Gf
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The statements at a level `α` -/

/-- **The reach test over every pseudo-base of level `α`**: every `ε`-number in `(P, N_α(P))` has a reach
`u·(1+q) + ζ` with `q ≤ α`, `ζ < u`. -/
def HcDownG (ρ α : Ordinal.{0}) : Prop :=
  ∀ P u : Ordinal.{0}, veblen α P = P → ρ < P → hcN α P < gq 1 ρ → InE u → P < u → u < hcN α P →
    ∃ q ζ, q ≤ α ∧ IsLh1 u (u * (1 + q) + ζ) ∧ ζ < u

/-- **Lemma IMG from `P` to `N_α(P)` over every pseudo-base `P` of level `α`.** -/
def HcNextG (ρ δ α : Ordinal.{0}) : Prop :=
  ∀ P : Ordinal.{0}, veblen α P = P → ρ < P → hcN α P < gq 1 ρ → (∀ v, v ≤ P → GnI ρ δ v) →
    ∀ v, v < hcN α P → GnI ρ δ v

theorem hc_nat_add_one (m : ℕ) : (m : Ordinal.{0}) + 1 = 1 + (m : Ordinal.{0}) := by
  rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]

section Step

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **The finite levels**: `HcDownG ρ k` and `HcNextG ρ δ k` for every `k ≥ 2` (`Hb.hb_DI`). -/
theorem hc_DI_fin (k : ℕ) (hk : 2 ≤ k) : HcDownG ρ (k : Ordinal.{0}) ∧ HcNextG ρ δ (k : Ordinal.{0}) := by
  obtain ⟨HD, HN⟩ := hb_DI h k hk
  refine ⟨fun P u hP hρP hNq hu hPu huN => ?_, fun P hP hρP hNq hle v hv => HN P hP hρP hNq hle v hv⟩
  obtain ⟨m, ζ, hm, hl, hζ⟩ := HD P u hP hρP hNq hu hPu huN
  refine ⟨(m : Ordinal.{0}), ζ, Nat.cast_le.2 hm, ?_, hζ⟩
  rw [← hc_nat_add_one]; exact hl

variable {α : Ordinal.{0}} (hα2 : 2 < α)
  (IH : ∀ γ, 2 ≤ γ → γ < α → HcDownG ρ γ ∧ HcNextG ρ δ γ)
include hα2 IH

/-- A gap `(φ(α, j), φ(α, j+1))` lies below `N_γ(φ(α, j))` for some `2 ≤ γ < α`, and `N_γ(φ(α, j)) ≤ φ(α, j+1)`. -/
theorem hc_gap2 {j u : Ordinal.{0}} (hju : veblen α j < u) (huj : u < veblen α (j + 1)) :
    ∃ γ, 2 ≤ γ ∧ γ < α ∧ u < hcN γ (veblen α j) ∧ hcN γ (veblen α j) ≤ veblen α (j + 1) ∧
      veblen γ (veblen α j) = veblen α j := by
  have hα0 : α ≠ 0 := (lt_of_le_of_lt zero_le hα2).ne'
  obtain ⟨γ, hγα, hu⟩ := hc_gap hα0 hju huj
  have hγ' : max γ 2 < α := max_lt hγα hα2
  refine ⟨max γ 2, le_max_right _ _, hγ', hu.trans_le (hcN_mono (le_max_left _ _) _), ?_,
    veblen_veblen_of_lt hγ' j⟩
  exact hcN_le (veblen_veblen_of_lt hγ' (j + 1)) ((isNormal_veblen α).strictMono (lt_add_one j))

/-- **The reach test in a gap**: every `ε`-number in `(φ(α, j), φ(α, j+1))` has a reach `u·(1+q) + ζ` with
`q < α`. -/
theorem hc_gapDown {j u : Ordinal.{0}} (hρQ : ρ < veblen α j) (hBq : veblen α (j + 1) < gq 1 ρ) (hu : InE u)
    (hju : veblen α j < u) (huj : u < veblen α (j + 1)) :
    ∃ q ζ, q < α ∧ IsLh1 u (u * (1 + q) + ζ) ∧ ζ < u := by
  obtain ⟨γ, hγ2, hγα, huN, hNB, hfix⟩ := hc_gap2 h hα2 IH hju huj
  obtain ⟨q, ζ, hq, hl, hζ⟩ := (IH γ hγ2 hγα).1 _ u hfix hρQ (hNB.trans_lt hBq) hu hju huN
  exact ⟨q, ζ, hq.trans_lt hγα, hl, hζ⟩

/-- **Lemma IMG in a gap**: Lemma IMG up to `φ(α, j)` gives it below `φ(α, j+1)`. -/
theorem hc_gapNext {j : Ordinal.{0}} (hρQ : ρ < veblen α j) (hBq : veblen α (j + 1) < gq 1 ρ)
    (hle : ∀ v, v ≤ veblen α j → GnI ρ δ v) : ∀ v, v < veblen α (j + 1) → GnI ρ δ v := by
  intro v hv
  rcases le_or_gt v (veblen α j) with hvQ | hQv
  · exact hle v hvQ
  obtain ⟨γ, hγ2, hγα, hvN, hNB, hfix⟩ := hc_gap2 h hα2 IH hQv hv
  exact (IH γ hγ2 hγα).2 _ hfix hρQ (hNB.trans_lt hBq) hle v hvN

omit hα2 IH in
/-- **The closed form over `P`**: `ϑᵖ(Ω₁·α + P + d) = φ(α, P+1+d)` below `N_α(P)`. -/
theorem hc_step_cfG {P d : Ordinal.{0}} (hα1 : 1 ≤ α) (hαw : α < ω ^ ω) (hP : veblen α P = P) (hρP : ρ < P)
    (hNq : hcN α P < gq 1 ρ) (hd : veblen α (P + 1 + d) < hcN α P) :
    glA α (P + d) ρ = veblen α (P + 1 + d) ∧ P + d < gq 1 ρ := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hPq : P < gq 1 ρ := (hcN_gt α P).trans hNq
  have hαq : α < gq 1 ρ := hαw.trans (hc_ww_lt_E (gm1_facts hρE hρ1).2.2.2)
  have hαP : α < P := (hαw.trans (hc_ww_lt_E hρE)).trans hρP
  have hi : P < veblen α (P + 1) := hc_lt_next hP
  have hnf : ∀ ν', ν' ≤ d → P + 1 + ν' < veblen α (P + 1 + ν') := fun ν' h' =>
    hc_nofixG hi le_self_add (((isNormal_veblen _).monotone ((add_le_add_iff_left _).2 h')).trans_lt hd)
  have hdq : P + d < gq 1 ρ :=
    (inE_indec (gm1_facts hρE hρ1).2.2.2).add_lt hPq
      ((((le_add_self : d ≤ P + 1 + d).trans_lt (hnf d le_rfl))).trans (hd.trans hNq))
  have hG0 : glA α P ρ = veblen α (P + 1) := hc_glA_fixG hρE hρ1 hα1 hαq hP hαP hρP hPq
  exact ⟨hc_glAV hρE hρ1 hα1 hαq hPq hG0 d hdq (fun ν' h' _ => hnf ν' h'), hdq⟩

/-- **THE STEP AT A LEVEL `2 < α < ω^ω`** (successor and limit alike): the reach test and Lemma IMG over every
pseudo-base of level `α`, given both at every level `2 ≤ γ < α`. -/
theorem hc_stepG (hαw : α < ω ^ ω) : HcDownG ρ α ∧ HcNextG ρ δ α := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hα1 : 1 ≤ α := one_le_two.trans hα2.le
  have hαq : α < gq 1 ρ := hαw.trans (hc_ww_lt_E (gm1_facts hρE hρ1).2.2.2)
  -- the points of level `α` over `P`
  have hpoint : ∀ P d, veblen α P = P → ρ < P → hcN α P < gq 1 ρ → veblen α (P + 1 + d) < hcN α P →
      IsLh1 (veblen α (P + 1 + d)) (veblen α (P + 1 + d) * (1 + α) + luZeta ρ α (P + d)) ∧
        luZeta ρ α (P + d) < veblen α (P + 1 + d) := by
    intro P d hP hρP hNq hd
    obtain ⟨hval, hdq⟩ := hc_step_cfG h hα1 hαw hP hρP hNq hd
    obtain ⟨hdT, hd1⟩ := gm1_T hρE hρ1 hdq
    have H := hc_lhG hρE hρ1 hα1 hαw hdT hd1
    rw [hval] at H
    exact H
  have hρj : ∀ P j, veblen α P = P → ρ < P → P + 1 ≤ j → ρ < veblen α j := fun P j hP hρP hPj =>
    hρP.trans ((hc_lt_next hP).trans_le ((isNormal_veblen _).monotone hPj))
  refine ⟨fun P u hP hρP hNq hu hPu huN => ?_, fun P hP hρP hNq hle => ?_⟩
  · -- the reach test
    have hBq : veblen α (P + 1) < gq 1 ρ := hc_next_lt_N.trans hNq
    rcases lt_or_ge u (veblen α (P + 1)) with h1 | h2
    · obtain ⟨q, ζ, hq, hl, hζ⟩ := hc_gapDown h hα2 IH (by rw [hP]; exact hρP) hBq hu (by rw [hP]; exact hPu) h1
      exact ⟨q, ζ, hq.le, hl, hζ⟩
    obtain ⟨j, hPj, hj1, hj2, hj1N⟩ := hc_floorG hP h2 huN
    rcases hj1.lt_or_eq with hju | hju
    · obtain ⟨q, ζ, hq, hl, hζ⟩ :=
        hc_gapDown h hα2 IH (hρj P j hP hρP hPj) (hj1N.trans hNq) hu hju hj2
      exact ⟨q, ζ, hq.le, hl, hζ⟩
    · obtain ⟨d, rfl⟩ := exists_add_of_le hPj
      obtain ⟨hL, hζ⟩ := hpoint P d hP hρP hNq (hju ▸ huN)
      rw [hju] at hL hζ
      exact ⟨α, _, le_rfl, hL, hζ⟩
  · -- Lemma IMG
    have hBq : veblen α (P + 1) < gq 1 ρ := hc_next_lt_N.trans hNq
    have hPq : P < gq 1 ρ := (hcN_gt α P).trans hNq
    have hαP : α < P := (hαw.trans (hc_ww_lt_E hρE)).trans hρP
    have hG0 : glA α P ρ = veblen α (P + 1) := hc_glA_fixG hρE hρ1 hα1 hαq hP hαP hρP hPq
    have hbelow1 : ∀ v, v < veblen α (P + 1) → GnI ρ δ v :=
      hc_gapNext h hα2 IH (by rw [hP]; exact hρP) hBq (by rw [hP]; exact hle)
    refine gnImg_of_eps h (fun v hv => gm1_T hρE hρ1 (hv.trans hNq)) (fun e he _ heB IHe => ?_)
    rcases lt_or_ge e (veblen α (P + 1)) with heS | hSe
    · exact hbelow1 e heS
    obtain ⟨j, hPj, hj1, hj2, hj1N⟩ := hc_floorG hP hSe heB
    rcases hj1.lt_or_eq with hje | hje
    · exact hc_gapNext h hα2 IH (hρj P j hP hρP hPj) (hj1N.trans hNq) (fun v hv => IHe v (hv.trans_lt hje)) e hj2
    obtain ⟨d, rfl⟩ := exists_add_of_le hPj
    have hdN : veblen α (P + 1 + d) < hcN α P := hje ▸ heB
    obtain ⟨hval, hdq⟩ := hc_step_cfG h hα1 hαw hP hρP hNq hdN
    obtain ⟨hdT, hd1⟩ := gm1_T hρE hρ1 hdq
    have he' : glA α (P + d) ρ = e := hval.trans hje
    have hnf : ∀ ν', ν' ≤ d → IsSuccLimit ν' → P + 1 + ν' < veblen α (P + 1 + ν') := fun ν' h' _ =>
      hc_nofixG (hc_lt_next hP) le_self_add
        (((isNormal_veblen _).monotone ((add_le_add_iff_left _).2 h')).trans_lt hdN)
    have IH' : ∀ u, u < glA α (P + d) ρ → GnI ρ δ u := fun u hu => IHe u (by rw [he'] at hu; exact hu)
    have hgapD : ∀ j' u, P + 1 ≤ j' → InE u → veblen α j' < u → u < veblen α (j' + 1) →
        veblen α (j' + 1) < gq 1 ρ → ∃ q' ζ, q' ≤ α ∧ IsLh1 u (u * (1 + q') + ζ) ∧ ζ < u ∧
          (q' = α → ζ < luZeta ρ α (P + d)) := by
      intro j' u hPj' hu h1 h2 hB
      obtain ⟨q, ζ, hq, hl, hζ⟩ := hc_gapDown h hα2 IH (hρj P j' hP hρP hPj') hB hu h1 h2
      exact ⟨q, ζ, hq.le, hl, hζ, fun e => absurd e hq.ne⟩
    rcases zero_or_succ_or_isSuccLimit d with h0 | ⟨d', hd'⟩ | hlim
    · -- the first point `φ(α, P+1)`: the reach test with `E' = P`
      subst h0
      have he0 : glA α (P + 0) ρ = veblen α (P + 1) := by rw [add_zero, hG0]
      have H := hc_img_downG h hα1 hαw hdT hd1 hρP (by rw [he0]; exact hc_lt_next hP)
        (fun u hu hPu huE => by
          rw [he0] at huE
          obtain ⟨q, ζ, hq, hl, hζ⟩ :=
            hc_gapDown h hα2 IH (by rw [hP]; exact hρP) hBq hu (by rw [hP]; exact hPu) huE
          exact ⟨q, ζ, hq.le, hl, hζ, fun e => absurd e hq.ne⟩) IH'
      rwa [he'] at H
    · -- successor: the reach test with `E'` the previous point
      have hd'' : d = d' + 1 := by rw [← hd', succ_eq_add_one]
      subst hd''
      set Q' := veblen α (P + 1 + d') with hQ'
      have heS : e = veblen α (P + 1 + d' + 1) := by rw [← hje, ← add_assoc]
      have hQ'e : Q' < e := by rw [heS, hQ']; exact (isNormal_veblen _).strictMono (lt_add_one _)
      have hρQ' : ρ < Q' := hρj P _ hP hρP le_self_add
      have H := hc_img_downG h hα1 hαw hdT hd1 hρQ' (by rw [he']; exact hQ'e)
        (fun u hu hQ'u huE => by
          rw [he', heS] at huE
          exact hgapD _ u le_self_add hu hQ'u huE (by rw [← heS]; exact heB.trans hNq)) IH'
      rwa [he'] at H
    · -- limit: the reach test with `E' = φ(α, P+1+c')`, `d = c' + ω^z`
      have hd0 : d ≠ 0 := hlim.bot_lt.ne'
      obtain ⟨c', hcs, -, hc'd⟩ := lg_split hd0
      set z := lg d with hzdef
      set E' := veblen α (P + 1 + c') with hE'def
      have hE'e : E' < e := by
        rw [← hje]; exact (isNormal_veblen _).strictMono ((add_lt_add_iff_left _).2 hc'd)
      have hSE' : veblen α (P + 1) ≤ E' := by rw [hE'def]; exact (isNormal_veblen _).monotone le_self_add
      have hρE' : ρ < E' := hρj P _ hP hρP le_self_add
      have hz' : luZeta ρ α (P + d) = z := hc_zetaG hρE hρ1 hα1 hαq hPq hG0 hdq hnf hlim
      have H := hc_img_downG h hα1 hαw hdT hd1 hρE' (by rw [he']; exact hE'e) (fun u hu hE'u huE => ?_) IH'
      · rwa [he'] at H
      rw [he'] at huE
      have huN : u < hcN α P := huE.trans heB
      obtain ⟨j', hPj', hj1', hj2', hj1N'⟩ := hc_floorG hP (hSE'.trans hE'u.le) huN
      have hcj : P + 1 + c' ≤ j' := by
        have : veblen α (P + 1 + c') < veblen α (j' + 1) := hE'u.trans hj2'
        exact Order.lt_add_one_iff.1 ((isNormal_veblen _).strictMono.lt_iff_lt.1 this)
      have hjE : j' < P + 1 + d := by
        have : veblen α j' < veblen α (P + 1 + d) := by rw [hje]; exact hj1'.trans_lt huE
        exact (isNormal_veblen _).strictMono.lt_iff_lt.1 this
      rcases hj1'.lt_or_eq with hju | hju
      · exact hgapD j' u hPj' hu hju hj2' (hj1N'.trans hNq)
      · obtain ⟨d'', rfl⟩ := exists_add_of_le hPj'
        have hc'd'' : c' < d'' := by
          rcases ((add_le_add_iff_left _).1 hcj).lt_or_eq with h' | h'
          · exact h'
          · exfalso; rw [← h'] at hju; exact absurd hju hE'u.ne
        have hd''d : d'' < d := (add_lt_add_iff_left _).1 hjE
        have hd''0 : d'' ≠ 0 := (lt_of_le_of_lt zero_le hc'd'').ne'
        obtain ⟨hL, hζu⟩ := hpoint P d'' hP hρP hNq (hju ▸ huN)
        rw [hju] at hL hζu
        have hζlg : luZeta ρ α (P + d'') ≤ lg d'' := lu_zeta_le_lg.trans (gz_lg_add P hd''0).le
        obtain ⟨δ', hδ'⟩ : ∃ δ', d'' = c' + δ' := ⟨d'' - c', (Ordinal.add_sub_cancel_of_le hc'd''.le).symm⟩
        have hδ0 : δ' ≠ 0 := by rintro rfl; rw [add_zero] at hδ'; exact absurd hδ' hc'd''.ne'
        have hδlt : δ' < ω ^ z := by
          have : c' + δ' < c' + ω ^ z := by rw [← hδ', ← hcs]; exact hd''d
          exact (add_lt_add_iff_left _).1 this
        have hlgd : lg d'' < z := by
          rw [hδ', gz_lg_add _ hδ0]
          by_contra hge; push Not at hge
          obtain ⟨δ'', hδs, -, -⟩ := lg_split hδ0
          have h1 : ω ^ z ≤ ω ^ lg δ' := opow_le_opow_right omega0_pos hge
          have h2 : ω ^ lg δ' ≤ δ' := (le_add_self (a := ω ^ lg δ') (b := δ'')).trans_eq hδs.symm
          exact absurd hδlt (not_lt.2 (h1.trans h2))
        exact ⟨α, _, le_rfl, hL, hζu, fun _ => by rw [hz']; exact hζlg.trans_lt hlgd⟩

end Step

/-! ## The induction on the level -/

section Ind

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **THE TRANSFINITE INDUCTION ON THE VEBLEN LEVEL**: `HcDownG ρ α` and `HcNextG ρ δ α` for every
`2 ≤ α < ω^ω`. -/
theorem hc_DI : ∀ α, 2 ≤ α → α < ω ^ ω → HcDownG ρ α ∧ HcNextG ρ δ α := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
  intro hα2 hαw
  rcases lt_or_ge α ω with hαω | hωα
  · obtain ⟨k, rfl⟩ := lt_omega0.1 hαω
    have hk : 2 ≤ k := by
      have : ((2 : ℕ) : Ordinal.{0}) ≤ (k : Ordinal.{0}) := by exact_mod_cast hα2
      exact_mod_cast this
    exact hc_DI_fin h k hk
  · have hα2' : 2 < α := (show (2 : Ordinal.{0}) < ω from natCast_lt_omega0 2).trans_le hωα
    exact hc_stepG h hα2' (fun γ hγ2 hγα => IH γ hγα hγ2 (hγα.trans hαw)) hαw

/-- **LEMMA IMG BELOW `N_α(Γ_{ρ+1})` FOR EVERY `α < ω^ω`.** -/
theorem hc_img_lvl {α : Ordinal.{0}} (hαw : α < ω ^ ω) : ∀ v, v < hcN α (lgG ρ) → GnI ρ δ v := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨-, hρG, -, hGE, -⟩ := lgG_facts hρE hρ1
  set α' := max α 2 with hα'
  have hα'w : α' < ω ^ ω := max_lt hαw ((natCast_lt_omega0 2).trans hc_om_lt_ww)
  have hα'G : α' < lgG ρ := hα'w.trans (hc_ww_lt_E hGE)
  have hα'1 : 1 ≤ α' := one_le_two.trans (le_max_right _ _)
  have hq := (gm1_facts hρE hρ1).2.2.2
  have hα'q : α' + 1 < gq 1 ρ := (ev_isSuccLimit_of_inE hq).add_one_lt (hα'w.trans (hc_ww_lt_E hq))
  have HN := (hc_DI h α' (le_max_right _ _) hα'w).2
  have H := HN (lgG ρ) (hc_G_fix hρE hρ1 hα'1 hα'G) hρG (hcN_G_lt hρE hρ1 hα'q) (fun v hv => ?_)
  · exact fun v hv => H v (hv.trans_le (hcN_mono (le_max_left _ _) _))
  rcases hv.lt_or_eq with hlt | rfl
  · exact gnI_lowG h hlt
  · exact gnI_G h

end Ind

/-! ## The bound `B_{ω^ω}(x) = φ(ω^ω, Γ_{x+1}+1)` -/

/-- **`B_{ω^ω}(x) = φ(ω^ω, Γ_{x+1}+1)`**, the least common fixed point of every `φ(α, ·)`, `α < ω^ω`, above
`Γ_{x+1}`. -/
noncomputable def hcBW (x : Ordinal.{0}) : Ordinal.{0} := veblen (ω ^ ω) (lgG x + 1)

section BW

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem hc_G_fixWW : veblen (ω ^ ω) (lgG x) = lgG x :=
  hc_G_fix hx hx1 hc_one_lt_ww.le (hc_ww_lt_E (lgG_facts hx hx1).2.2.2.1)

/-- **`B_{ω^ω}(x) = ϑˣ(Ω₁·ω^ω + Γ_{x+1}) < Γ_{x+2}`.** -/
theorem hcBW_lt1 : hcBW x < gq 1 x := by
  have hq := (gm1_facts hx hx1).2.2.2
  have hwq : ω ^ ω < gq 1 x := hc_ww_lt_E hq
  obtain ⟨hwT, hw1⟩ := gm1_T hx hx1 hwq
  obtain ⟨hGT, -, hG1, hGE, -⟩ := lgG_facts hx hx1
  have e := hc_glA_GG hx hx1 hc_one_lt_ww.le (hc_ww_lt_E hGE)
  unfold hcBW
  rw [← e]
  exact lgVt_lt_low hx hx1 hwT hw1 hGT hG1 (gm1_one_T hx hx1).1 (gm1_one_T hx hx1).2 hwq (mg_lgG_lt_G1 hx hx1)

/-- `N_α(Γ_{x+1}) ≤ B_{ω^ω}(x)` for `α < ω^ω`; `B_{ω+1}(x) < B_{ω^ω}(x)`. -/
theorem hcN_le_BW {α : Ordinal.{0}} (hαw : α < ω ^ ω) : hcN α (lgG x) ≤ hcBW x :=
  hcN_le (veblen_veblen_of_lt hαw _) ((hc_lt_next (hc_G_fixWW hx hx1)))

theorem hc_B1_lt_BW : hcB1 x < hcBW x := by
  have hω1 : ω + 1 < ω ^ ω := hc_ww_indec.add_lt hc_om_lt_ww hc_one_lt_ww
  calc hcB1 x = hcN ω (lgG x) := rfl
    _ < hcN (ω + 1) (lgG x) := by
      have h1 : hcN ω (lgG x) ≤ veblen (ω + 1) (lgG x + 1) :=
        hcN_le (veblen_veblen_of_lt (lt_add_one ω) _) ((lt_add_one _).trans_le (right_le_veblen _ _))
      have h2 : lgG x + 1 < hcN (ω + 1) (lgG x) := (hcN_lim _ _).add_one_lt (hcN_gt _ _)
      have h3 := (isNormal_veblen (ω + 1)).strictMono h2
      rw [hcN_fix] at h3
      exact h1.trans_lt h3
    _ ≤ hcBW x := hcN_le_BW hx hx1 hω1

/-- `B_ω(x) ≤ B_{ω^ω}(x)`. -/
theorem hc_Bw_le_BW : hbBw x ≤ hcBW x := (hc_Bw_lt_B1 hx hx1).le.trans (hc_B1_lt_BW hx hx1).le

end BW

section ImgBW

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG BELOW `B_{ω^ω}(ρ) = φ(ω^ω, Γ_{ρ+1}+1)`.** -/
theorem hc_img_BW : ∀ v, v < hcBW ρ → GnI ρ δ v := by
  intro v hv
  obtain ⟨-, -, -, hGE, -⟩ := lgG_facts h.ρE h.ρ1
  rcases le_or_gt v (lgG ρ) with hvG | hGv
  · rcases hvG.lt_or_eq with hlt | rfl
    · exact gnI_lowG h hlt
    · exact gnI_G h
  have hfix := hc_G_fixWW h.ρE h.ρ1
  obtain ⟨γ, hγ, hvN⟩ := hc_gap (opow_pos ω omega0_pos).ne' (by rw [hfix]; exact hGv) hv
  rw [hfix] at hvN
  exact hc_img_lvl h hγ v hvN

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW `B_{ω^ω}(ρ)`.** -/
theorem hc_pkg_BW {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : T ρ < hcBW ρ) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (hc_img_BW h _ hT) hex

end ImgBW

end Googology.Trans.PoR.InaccPsi.R2.Hc
