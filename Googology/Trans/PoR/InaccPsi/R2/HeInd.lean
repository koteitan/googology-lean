import Googology.Trans.PoR.InaccPsi.R2.HeImg

/-!
# HeInd: LEMMA IMG BELOW `φ(Γ_{ρ+1}, 1)`, BY ONE TRANSFINITE INDUCTION OVER EVERY LEVEL `2 ≤ α < Γ_{ρ+2}`

`Hc.HcLInd` runs the induction on the Veblen level over the constant levels `α < ρ` only (bound `B_ρ(ρ) =
φ(ρ, Γ_{ρ+1}+1)`).  With Lemma IMG by the reach test going down at EVERY level (`He.he_img_down`, built on the
copy lemma `He.he_wz_mul` and `π(u·c) = π(u)·π(c)`, `He.he_pi_mul`) the same step (`Hc.hc_gap2L`, `Hc.hc_gapDownL`,
`Hc.hc_gapNextL`, the closed form `ϑᵖ(Ω₁·α + P + d) = φ(α, P+1+d)`) runs over every level `2 < α < Γ_{ρ+2}`
(`he_stepL`, `he_DI`).  In particular at the level `ρ` itself (`he_DR`: the reach test and Lemma IMG over every
pseudo-base of level `ρ`), and Lemma IMG holds below `N_α(Γ_{ρ+1})` for every `α < Γ_{ρ+1}` (`he_img_lvl`), hence
below `φ(Γ_{ρ+1}, 1)`, the least common fixed point of every `φ(α, ·)`, `α < Γ_{ρ+1}`, above `Γ_{ρ+1}`
(`he_img_BG`), and Lemma IMG (gated) for a specified function below it (`he_pkg_BG`).  `B_ρ(ρ) < N_ρ(Γ_{ρ+1}) <
φ(Γ_{ρ+1}, 1)` (`he_BR_lt_NR`, `he_NR_lt_BG`).

* `he_lt_fix`, `he_G_sc` (**`φ(Γ_{x+1}, 0) = Γ_{x+1}`**), `he_step_cf`, `he_stepL` (**THE STEP AT EVERY LEVEL**),
  `he_DI` (**THE TRANSFINITE INDUCTION OVER EVERY LEVEL `α < Γ_{ρ+2}`**), `he_DR` (**THE LEVEL `ρ`**), `he_img_lvl`,
  `he_img_NR` (**LEMMA IMG BELOW `N_ρ(Γ_{ρ+1})`**), `he_img_BG` (**LEMMA IMG BELOW `φ(Γ_{ρ+1}, 1)`**), `he_pkg_BG`,
  `he_BR_lt_NR`, `he_NR_lt_BG`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.He

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gw
  Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Hb Googology.Trans.PoR.InaccPsi.R2.Gz
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gb

/-- A fixed point `P` of `φ(α, ·)` lies above `α`. -/
theorem he_lt_fix {α P : Ordinal.{0}} (hP : veblen α P = P) : α < P := by
  have h1 : α ≤ P := hP ▸ left_le_veblen α P
  rcases h1.lt_or_eq with h | h
  · exact h
  · exfalso; subst h; have := lt_veblen α; rw [hP] at this; exact lt_irrefl _ this

/-- **`φ(Γ_{x+1}, 0) = Γ_{x+1}`**: `Γ_{x+1}` is strongly critical. -/
theorem he_G_sc {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : veblen (lgG x) 0 = lgG x := by
  obtain ⟨-, hxG, -, hGE, -⟩ := lgG_facts hx hx1
  have hG0 : lgG x ≠ 0 := (hx.pos.trans hxG).ne'
  have hmem : lgG x ∈ range (veblen (lgG x)) := by
    refine (mem_range_veblen hG0).2 (fun b hb => ?_)
    rcases eq_or_ne b 0 with rfl | hb0
    · rw [veblen_zero_apply]; exact hGE
    · exact hc_G_fix hx hx1 (one_le_iff_ne_zero.2 hb0) hb
  obtain ⟨a, ha⟩ := hmem
  rcases eq_or_ne a 0 with rfl | ha0
  · exact ha
  · exfalso
    have h1 := (isNormal_veblen (lgG x)).strictMono (pos_iff_ne_zero.2 ha0)
    rw [ha] at h1
    exact absurd ((left_le_veblen (lgG x) 0).trans_lt h1) (lt_irrefl _)

section Step

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **The closed form over `P`** at every level `1 ≤ α < Γ_{ρ+2}`: `ϑᵖ(Ω₁·α + P + d) = φ(α, P+1+d)` below
`N_α(P)`. -/
theorem he_step_cf {α P d : Ordinal.{0}} (hα1 : 1 ≤ α) (hαq : α < gq 1 ρ) (hP : veblen α P = P) (hρP : ρ < P)
    (hNq : hcN α P < gq 1 ρ) (hd : veblen α (P + 1 + d) < hcN α P) :
    glA α (P + d) ρ = veblen α (P + 1 + d) ∧ P + d < gq 1 ρ := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hPq : P < gq 1 ρ := (hcN_gt α P).trans hNq
  have hαP : α < P := he_lt_fix hP
  have hnf : ∀ ν', ν' ≤ d → P + 1 + ν' < veblen α (P + 1 + ν') := fun ν' h' =>
    hc_nofixG (hc_lt_next hP) le_self_add (((isNormal_veblen _).monotone ((add_le_add_iff_left _).2 h')).trans_lt hd)
  have hdq : P + d < gq 1 ρ :=
    (inE_indec (gm1_facts hρE hρ1).2.2.2).add_lt hPq
      ((((le_add_self : d ≤ P + 1 + d).trans_lt (hnf d le_rfl))).trans (hd.trans hNq))
  have hG0 : glA α P ρ = veblen α (P + 1) := hc_glA_fixG hρE hρ1 hα1 hαq hP hαP hρP hPq
  exact ⟨hc_glAV hρE hρ1 hα1 hαq hPq hG0 d hdq (fun ν' h' _ => hnf ν' h'), hdq⟩

variable {α : Ordinal.{0}} (hα2 : 2 < α)
  (IH : ∀ γ, 2 ≤ γ → γ < α → HcDownL ρ γ ∧ HcNextG ρ δ γ)
include hα2 IH

/-- **THE STEP AT EVERY LEVEL `2 < α < Γ_{ρ+2}`** (successor and limit, constant or not): the reach test and Lemma
IMG over every pseudo-base of level `α`, given both at every level `2 ≤ γ < α`. -/
theorem he_stepL (hαq : α < gq 1 ρ) : HcDownL ρ α ∧ HcNextG ρ δ α := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hα1 : 1 ≤ α := one_le_two.trans hα2.le
  obtain ⟨hαT, hαΩ⟩ := gm1_T hρE hρ1 hαq
  -- the points of level `α` over `P`
  have hpoint : ∀ P d, veblen α P = P → ρ < P → hcN α P < gq 1 ρ → veblen α (P + 1 + d) < hcN α P →
      IsLh1 (veblen α (P + 1 + d)) (veblen α (P + 1 + d) * (1 + α) + hcE α + luZeta ρ α (P + d)) ∧
        luZeta ρ α (P + d) < veblen α (P + 1 + d) := by
    intro P d hP hρP hNq hd
    obtain ⟨hval, hdq⟩ := he_step_cf h hα1 hαq hP hρP hNq hd
    obtain ⟨hdT, hd1⟩ := gm1_T hρE hρ1 hdq
    obtain ⟨H1, H2, -⟩ := he_lhq hρE hρ1 hα1 hαT hαΩ hdT hd1
    rw [hval] at H1 H2
    exact ⟨H1, H2⟩
  have hρj : ∀ P j, veblen α P = P → ρ < P → P + 1 ≤ j → ρ < veblen α j := fun P j hP hρP hPj =>
    hρP.trans ((hc_lt_next hP).trans_le ((isNormal_veblen _).monotone hPj))
  have hαj : ∀ P j, veblen α P = P → P + 1 ≤ j → α < veblen α j := fun P j hP hPj =>
    (he_lt_fix hP).trans ((hc_lt_next hP).trans_le ((isNormal_veblen _).monotone hPj))
  refine ⟨fun P u hP hρP hNq hu hPu huN => ?_, fun P hP hρP hNq hle => ?_⟩
  · -- the reach test
    have hBq : veblen α (P + 1) < gq 1 ρ := hc_next_lt_N.trans hNq
    rcases lt_or_ge u (veblen α (P + 1)) with h1 | h2
    · obtain ⟨q, ζ, hq, hl, hζ⟩ := hc_gapDownL h hα2 IH (by rw [hP]; exact hρP) hBq hu (by rw [hP]; exact hPu) h1
      exact ⟨q, ζ, hq.le, hl, hζ⟩
    obtain ⟨j, hPj, hj1, hj2, hj1N⟩ := hc_floorG hP h2 huN
    rcases hj1.lt_or_eq with hju | hju
    · obtain ⟨q, ζ, hq, hl, hζ⟩ :=
        hc_gapDownL h hα2 IH (hρj P j hP hρP hPj) (hj1N.trans hNq) hu hju hj2
      exact ⟨q, ζ, hq.le, hl, hζ⟩
    · obtain ⟨d, rfl⟩ := exists_add_of_le hPj
      obtain ⟨hL, hζ⟩ := hpoint P d hP hρP hNq (hju ▸ huN)
      rw [hju] at hL hζ
      exact ⟨α, _, le_rfl, hL, hζ⟩
  · -- Lemma IMG
    have hBq : veblen α (P + 1) < gq 1 ρ := hc_next_lt_N.trans hNq
    have hPq : P < gq 1 ρ := (hcN_gt α P).trans hNq
    have hαP : α < P := he_lt_fix hP
    have hG0 : glA α P ρ = veblen α (P + 1) := hc_glA_fixG hρE hρ1 hα1 hαq hP hαP hρP hPq
    have hbelow1 : ∀ v, v < veblen α (P + 1) → GnI ρ δ v :=
      hc_gapNextL h hα2 IH (by rw [hP]; exact hρP) hBq (by rw [hP]; exact hle)
    refine gnImg_of_eps h (fun v hv => gm1_T hρE hρ1 (hv.trans hNq)) (fun e he _ heB IHe => ?_)
    rcases lt_or_ge e (veblen α (P + 1)) with heS | hSe
    · exact hbelow1 e heS
    obtain ⟨j, hPj, hj1, hj2, hj1N⟩ := hc_floorG hP hSe heB
    rcases hj1.lt_or_eq with hje | hje
    · exact hc_gapNextL h hα2 IH (hρj P j hP hρP hPj) (hj1N.trans hNq) (fun v hv => IHe v (hv.trans_lt hje)) e hj2
    obtain ⟨d, rfl⟩ := exists_add_of_le hPj
    have hdN : veblen α (P + 1 + d) < hcN α P := hje ▸ heB
    obtain ⟨hval, hdq⟩ := he_step_cf h hα1 hαq hP hρP hNq hdN
    obtain ⟨hdT, hd1⟩ := gm1_T hρE hρ1 hdq
    have he' : glA α (P + d) ρ = e := hval.trans hje
    have hnf : ∀ ν', ν' ≤ d → IsSuccLimit ν' → P + 1 + ν' < veblen α (P + 1 + ν') := fun ν' h' _ =>
      hc_nofixG (hc_lt_next hP) le_self_add
        (((isNormal_veblen _).monotone ((add_le_add_iff_left _).2 h')).trans_lt hdN)
    have IH' : ∀ u, u < glA α (P + d) ρ → GnI ρ δ u := fun u hu => IHe u (by rw [he'] at hu; exact hu)
    have hgapD : ∀ j' u, P + 1 ≤ j' → InE u → veblen α j' < u → u < veblen α (j' + 1) →
        veblen α (j' + 1) < gq 1 ρ → ∃ q' ζ, q' ≤ α ∧ IsLh1 u (u * (1 + q') + hcE q' + ζ) ∧ ζ < u ∧
          (q' = α → ζ < luZeta ρ α (P + d)) := by
      intro j' u hPj' hu h1 h2 hB
      obtain ⟨q, ζ, hq, hl, hζ⟩ := hc_gapDownL h hα2 IH (hρj P j' hP hρP hPj') hB hu h1 h2
      exact ⟨q, ζ, hq.le, hl, hζ, fun e => absurd e hq.ne⟩
    rcases zero_or_succ_or_isSuccLimit d with h0 | ⟨d', hd'⟩ | hlim
    · -- the first point `φ(α, P+1)`: the reach test with `E' = P`
      subst h0
      have he0 : glA α (P + 0) ρ = veblen α (P + 1) := by rw [add_zero, hG0]
      have H := he_img_down h hα1 hαT hαΩ hdT hd1 hρP hαP (by rw [he0]; exact hc_lt_next hP)
        (fun u hu hPu huE => by
          rw [he0] at huE
          obtain ⟨q, ζ, hq, hl, hζ⟩ :=
            hc_gapDownL h hα2 IH (by rw [hP]; exact hρP) hBq hu (by rw [hP]; exact hPu) huE
          exact ⟨q, ζ, hq.le, hl, hζ, fun e => absurd e hq.ne⟩) IH'
      rwa [he'] at H
    · -- successor: the reach test with `E'` the previous point
      have hd'' : d = d' + 1 := by rw [← hd', succ_eq_add_one]
      subst hd''
      set Q' := veblen α (P + 1 + d') with hQ'
      have heS : e = veblen α (P + 1 + d' + 1) := by rw [← hje, ← add_assoc]
      have hQ'e : Q' < e := by rw [heS, hQ']; exact (isNormal_veblen _).strictMono (lt_add_one _)
      have hρQ' : ρ < Q' := hρj P _ hP hρP le_self_add
      have hαQ' : α < Q' := hαj P _ hP le_self_add
      have H := he_img_down h hα1 hαT hαΩ hdT hd1 hρQ' hαQ' (by rw [he']; exact hQ'e)
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
      have hαE' : α < E' := hαj P _ hP le_self_add
      have hz' : luZeta ρ α (P + d) = z := hc_zetaG hρE hρ1 hα1 hαq hPq hG0 hdq hnf hlim
      have H := he_img_down h hα1 hαT hαΩ hdT hd1 hρE' hαE' (by rw [he']; exact hE'e)
        (fun u hu hE'u huE => ?_) IH'
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

/-- **THE TRANSFINITE INDUCTION ON THE VEBLEN LEVEL**: `HcDownL ρ α` and `HcNextG ρ δ α` for every level
`2 ≤ α < Γ_{ρ+2}`. -/
theorem he_DI : ∀ α, 2 ≤ α → α < gq 1 ρ → HcDownL ρ α ∧ HcNextG ρ δ α := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
  intro hα2 hαq
  rcases lt_or_ge α ω with hαω | hωα
  · obtain ⟨k, rfl⟩ := lt_omega0.1 hαω
    have hk : 2 ≤ k := by
      have : ((2 : ℕ) : Ordinal.{0}) ≤ (k : Ordinal.{0}) := by exact_mod_cast hα2
      exact_mod_cast this
    exact hc_DIL_fin h k hk
  · have hα2' : 2 < α := (show (2 : Ordinal.{0}) < ω from natCast_lt_omega0 2).trans_le hωα
    exact he_stepL h hα2' (fun γ hγ2 hγα => IH γ hγα hγ2 (hγα.trans hαq)) hαq

/-- **THE LEVEL `ρ`**: the reach test and Lemma IMG over every pseudo-base of level `ρ`. -/
theorem he_DR : HcDownL ρ ρ ∧ HcNextG ρ δ ρ := by
  have hρE := h.ρE
  have hρ2 : (2 : Ordinal.{0}) ≤ ρ := ((natCast_lt_omega0 2).trans (omega0_lt_inE hρE)).le
  exact he_DI h ρ hρ2 (gm1_facts hρE h.ρ1).2.1

/-- **LEMMA IMG BELOW `N_α(Γ_{ρ+1})` FOR EVERY LEVEL `α < Γ_{ρ+1}`.** -/
theorem he_img_lvl {α : Ordinal.{0}} (hαG : α < lgG ρ) : ∀ v, v < hcN α (lgG ρ) → GnI ρ δ v := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨-, hρG, -, -, -⟩ := lgG_facts hρE hρ1
  set α' := max α 2 with hα'
  have hα'G : α' < lgG ρ := max_lt hαG ((natCast_lt_omega0 2).trans ((omega0_lt_inE hρE).trans hρG))
  have hGq := mg_lgG_lt_G1 hρE hρ1
  have hα'1 : 1 ≤ α' := one_le_two.trans (le_max_right _ _)
  have hq := (gm1_facts hρE hρ1).2.2.2
  have hα'q : α' + 1 < gq 1 ρ := (ev_isSuccLimit_of_inE hq).add_one_lt (hα'G.trans hGq)
  have HN := (he_DI h α' (le_max_right _ _) (hα'G.trans hGq)).2
  have H := HN (lgG ρ) (hc_G_fix hρE hρ1 hα'1 hα'G) hρG (hcN_G_lt hρE hρ1 hα'q) (fun v hv => ?_)
  · exact fun v hv => H v (hv.trans_le (hcN_mono (le_max_left _ _) _))
  rcases hv.lt_or_eq with hlt | rfl
  · exact gnI_lowG h hlt
  · exact gnI_G h

/-- **LEMMA IMG BELOW `N_ρ(Γ_{ρ+1}) = φ(ρ+1, Γ_{ρ+1}+1)`** (the level `ρ`). -/
theorem he_img_NR : ∀ v, v < hcN ρ (lgG ρ) → GnI ρ δ v :=
  he_img_lvl h (lgG_facts h.ρE h.ρ1).2.1

/-- **LEMMA IMG BELOW `φ(Γ_{ρ+1}, 1)`**, the least common fixed point of every `φ(α, ·)`, `α < Γ_{ρ+1}`, above
`Γ_{ρ+1}`. -/
theorem he_img_BG : ∀ v, v < veblen (lgG ρ) 1 → GnI ρ δ v := by
  intro v hv
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨-, hρG, -, -, -⟩ := lgG_facts hρE hρ1
  rcases le_or_gt v (lgG ρ) with hvG | hGv
  · rcases hvG.lt_or_eq with hlt | rfl
    · exact gnI_lowG h hlt
    · exact gnI_G h
  have hsc := he_G_sc hρE hρ1
  have hG0 : lgG ρ ≠ 0 := (hρE.pos.trans hρG).ne'
  obtain ⟨γ, hγ, hvN⟩ := hc_gap hG0 (by rw [hsc]; exact hGv) (by rw [zero_add]; exact hv)
  rw [hsc] at hvN
  exact he_img_lvl h hγ v hvN

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW `φ(Γ_{ρ+1}, 1)`.** -/
theorem he_pkg_BG {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : T ρ < veblen (lgG ρ) 1) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (he_img_BG h _ hT) hex

end Ind

/-! ## The bounds -/

section Bounds

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`B_x(x) = φ(x, Γ_{x+1}+1) < N_x(Γ_{x+1})`.** -/
theorem he_BR_lt_NR : hcBR x < hcN x (lgG x) := by
  obtain ⟨-, hxG, -, -, -⟩ := lgG_facts hx hx1
  have h1x : (1 : Ordinal.{0}) ≤ x := one_lt_omega0.le.trans (omega0_lt_inE hx).le
  have hfix : veblen x (lgG x) = lgG x := hc_G_fix hx hx1 h1x hxG
  have h1 : lgG x + 1 < hcN x (lgG x) := (hcN_lim x (lgG x)).add_one_lt (hcN_gt x (lgG x))
  have h2 := (isNormal_veblen x).strictMono h1
  rw [hcN_fix] at h2
  exact h2

/-- **`N_x(Γ_{x+1}) < φ(Γ_{x+1}, 1)`.** -/
theorem he_NR_lt_BG : hcN x (lgG x) < veblen (lgG x) 1 := by
  obtain ⟨-, hxG, -, hGE, -⟩ := lgG_facts hx hx1
  have hsc := he_G_sc hx hx1
  have hG0 : lgG x ≠ 0 := (hx.pos.trans hxG).ne'
  have hx1G : x + 1 < lgG x := (ev_isSuccLimit_of_inE hGE).add_one_lt hxG
  have hGB : lgG x < veblen (lgG x) 1 := by
    have := (isNormal_veblen (lgG x)).strictMono (zero_lt_one' Ordinal.{0}); rwa [hsc] at this
  have hG1 : lgG x + 1 < veblen (lgG x) 1 :=
    (ev_isSuccLimit_of_inE (Gg.gg_veblen_eps hG0)).add_one_lt hGB
  have hle : hcN x (lgG x) ≤ veblen (x + 1) (lgG x + 1) :=
    hcN_le (veblen_veblen_of_lt (lt_add_one x) _) ((lt_add_one _).trans_le (right_le_veblen _ _))
  refine hle.trans_lt ?_
  have h2 := (isNormal_veblen (x + 1)).strictMono hG1
  rwa [veblen_veblen_of_lt hx1G] at h2

end Bounds

end Googology.Trans.PoR.InaccPsi.R2.He
