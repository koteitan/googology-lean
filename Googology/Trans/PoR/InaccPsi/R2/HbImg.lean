import Googology.Trans.PoR.InaccPsi.R2.HbLev

/-!
# HbImg: LEMMA IMG BELOW `B_{k+1}(ρ)` FOR EVERY FINITE `k`, BY ONE INDUCTION ON THE VEBLEN LEVEL

Over a pseudo-base `P` of level `k` (a fixed point of `φ(k, ·)`), every `ε`-number `u ∈ (P, N_k(P))` has a reach
`u·(m+1) + ζ` with `m ≤ k`, `ζ < u` (**`HbDown k`**), and Lemma IMG up to `P` gives Lemma IMG below `N_k(P)`
(**`HbNext k`**).  Both hold at `k = 2` (`Ha.ha_down_Pall`, `Ha.ha_img_next`) and pass from `k` to `k+1`: the
interval `[N_k(P), N_{k+1}(P))` consists of the points `φ(k+1, i₀ + d)` of level `k+1` (`φ(k+1, i₀) = N_k(P)`,
closed form `Hb.hb_glAV`, no fixed point of `φ(k+1,·)` by `Hb.hb_nofixV`) and the intervals between two consecutive
ones, which are `(Q, N_k(Q))` for the pseudo-bases `Q = φ(k+1, j)` of level `k`.  At the points: the reach test going
down (`Ha.ha_img_down`, generic in the level) with `E' = φ(k+1, i₀ + d')` at successors and `E' = φ(k+1, i₀ + c')`,
`d = c' + ω^z`, at limits (`hb_lev_glZeta`: `glZeta ρ (k+1) (P + d) = lg d`).  The steps `hb_downStep`,
`hb_imgStep` take any `P` with `ϑᵖ(Ω₁·(k+1) + P) = N_k(P)` (also `P = Γ_{ρ+1}`, `Hb.hb_glA_G`), so the same induction
gives Lemma IMG below `B_{k+1}(ρ) = N_k(Γ_{ρ+1})` for every `k` (**`hb_img_B`**; `N_2(Γ_{ρ+1}) = B₃(ρ)`,
`N_3(Γ_{ρ+1}) = B₄(ρ)`), hence below `B_ω(ρ) = sup_k B_{k+1}(ρ)` (`hb_img_Bw`), and Lemma IMG (gated, for a specified
function) below them (`hb_pkg_B`, `hb_pkg_Bw`).

* `HbDown`, `HbNext`, `hb_lev_glZeta`, `hb_downStep`, `hb_imgStep`, `hb_DI` (**THE INDUCTION ON THE LEVEL**),
  `hb_down`, `hb_img_next`, `hbN_G_lt`, `hb_img_B` (**LEMMA IMG BELOW `B_{k+1}(ρ)`, EVERY `k`**), `hbBw`,
  `hb_img_Bw`, `hb_pkg_B`, `hb_pkg_Bw`, `hb_N3_eq` (`N_3(Γ_{x+1}) = B₄(x)`).

No new axiom.  New definitions: `HbDown`, `HbNext`, `hbBw`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hb

open Googology.Trans.PoR.InaccPsi.R2.Gj Googology.Trans.PoR.InaccPsi.R2.Gh

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The statements -/

/-- **The reach test over every pseudo-base of level `k`.** -/
def HbDown (ρ : Ordinal.{0}) (k : ℕ) : Prop :=
  ∀ P u : Ordinal.{0}, veblen (k : Ordinal.{0}) P = P → ρ < P → hbN k P < gq 1 ρ → InE u → P < u → u < hbN k P →
    ∃ m : ℕ, ∃ ζ, m ≤ k ∧ IsLh1 u (u * ((m : Ordinal.{0}) + 1) + ζ) ∧ ζ < u

/-- **Lemma IMG from `P` to `N_k(P)` over every pseudo-base of level `k`.** -/
def HbNext (ρ δ : Ordinal.{0}) (k : ℕ) : Prop :=
  ∀ P : Ordinal.{0}, veblen (k : Ordinal.{0}) P = P → ρ < P → hbN k P < gq 1 ρ → (∀ v, v ≤ P → GnI ρ δ v) →
    ∀ v, v < hbN k P → GnI ρ δ v

section Steps

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- The data of a step from level `k` to `k+1` over `P`: `ϑᵖ(Ω₁·(k+1) + P) = N_k(P) = φ(k+1, i₀)`, the closed form
below `N_{k+1}(P)`. -/
theorem hb_step_cf (k : ℕ) {P i0 : Ordinal.{0}} (hP0 : glA ((k + 1 : ℕ) : Ordinal.{0}) P ρ = hbN k P)
    (hi0 : veblen ((k + 1 : ℕ) : Ordinal.{0}) i0 = hbN k P) (hPq : P < gq 1 ρ) (hHq : hbN (k + 1) P < gq 1 ρ)
    {d : Ordinal.{0}} (hd : veblen ((k + 1 : ℕ) : Ordinal.{0}) (i0 + d) < hbN (k + 1) P) :
    glA ((k + 1 : ℕ) : Ordinal.{0}) (P + d) ρ = veblen ((k + 1 : ℕ) : Ordinal.{0}) (i0 + d) ∧ P + d < gq 1 ρ := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hnf : ∀ ν', ν' ≤ d → i0 + ν' < veblen ((k + 1 : ℕ) : Ordinal.{0}) (i0 + ν') := fun ν' h' =>
    hb_nofixV k hi0 le_self_add (((isNormal_veblen _).monotone ((add_le_add_iff_left _).2 h')).trans_lt hd)
  have hdq : P + d < gq 1 ρ :=
    (inE_indec (gm1_facts hρE hρ1).2.2.2).add_lt hPq
      ((((le_add_self : d ≤ i0 + d).trans_lt (hnf d le_rfl))).trans (hd.trans hHq))
  exact ⟨hb_glAV hρE hρ1 k hPq (by rw [hP0, hi0]) d hdq (fun ν' h' _ => hnf ν' h'), hdq⟩

/-- **The reach of a point of level `k+1` over `P`**: `φ(k+1, i₀ + d)` (below `N_{k+1}(P)`) has reach `u·(k+2) + ζ`,
`ζ = glZeta ρ (k+1) (P + d) < u`. -/
theorem hb_step_lh (k : ℕ) {P i0 : Ordinal.{0}} (hP0 : glA ((k + 1 : ℕ) : Ordinal.{0}) P ρ = hbN k P)
    (hi0 : veblen ((k + 1 : ℕ) : Ordinal.{0}) i0 = hbN k P) (hρP : ρ < P) (hPq : P < gq 1 ρ)
    (hHq : hbN (k + 1) P < gq 1 ρ) {d : Ordinal.{0}}
    (hd : veblen ((k + 1 : ℕ) : Ordinal.{0}) (i0 + d) < hbN (k + 1) P) :
    IsLh1 (veblen ((k + 1 : ℕ) : Ordinal.{0}) (i0 + d))
      (veblen ((k + 1 : ℕ) : Ordinal.{0}) (i0 + d) * (((k + 1 : ℕ) : Ordinal.{0}) + 1) +
        glZeta ρ (k + 1) (P + d)) ∧
      glZeta ρ (k + 1) (P + d) < veblen ((k + 1 : ℕ) : Ordinal.{0}) (i0 + d) := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨hval, hdq⟩ := hb_step_cf h k hP0 hi0 hPq hHq hd
  obtain ⟨hdT, hd1⟩ := gm1_T hρE hρ1 hdq
  have hL := gl_lh_th (k := k + 1) hρE hρ1 (Nat.succ_le_succ (Nat.zero_le k)) hdT hd1
  have hv : vt ρ (Om1 * ((k + 1 : ℕ) : Ordinal.{0}) + (P + d)) = veblen ((k + 1 : ℕ) : Ordinal.{0}) (i0 + d) := hval
  rw [hv] at hL
  obtain ⟨hkT, hk1⟩ := hb_lev_T hρE hρ1 (k + 1)
  obtain ⟨-, -, -, -, -, htu⟩ := glA_facts hρE hρ1 (hb_one_le k) hkT hk1 hdT hd1
  rw [hval] at htu
  have hP0' : P + d ≠ 0 := ((hρE.pos.trans hρP).trans_le le_self_add).ne'
  refine ⟨?_, ((gz_glZeta_le ρ _ (k + 1)).trans (lg_le hP0')).trans_lt htu⟩
  have e : ((k + 1 + 1 : ℕ) : Ordinal.{0}) = ((k + 1 : ℕ) : Ordinal.{0}) + 1 := by push_cast; rfl
  rw [e] at hL
  exact hL

/-- **`glZeta ρ (k+1) (P + d) = lg d`** at a limit `d` (`φ(k+1, i₀ + d)` below `N_{k+1}(P)`). -/
theorem hb_lev_glZeta (k : ℕ) {P i0 d : Ordinal.{0}} (hP0 : glA ((k + 1 : ℕ) : Ordinal.{0}) P ρ = hbN k P)
    (hi0 : veblen ((k + 1 : ℕ) : Ordinal.{0}) i0 = hbN k P) (hPq : P < gq 1 ρ) (hHq : hbN (k + 1) P < gq 1 ρ)
    (hlim : IsSuccLimit d) (hd : veblen ((k + 1 : ℕ) : Ordinal.{0}) (i0 + d) < hbN (k + 1) P) :
    glZeta ρ (k + 1) (P + d) = lg d := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hd0 : d ≠ 0 := hlim.bot_lt.ne'
  obtain ⟨hval, hdq⟩ := hb_step_cf h k hP0 hi0 hPq hHq hd
  obtain ⟨hdT, hd1⟩ := gm1_T hρE hρ1 hdq
  obtain ⟨hkT, hk1⟩ := hb_lev_T hρE hρ1 (k + 1)
  obtain ⟨-, -, -, -, -, htE⟩ := glA_facts hρE hρ1 (hb_one_le k) hkT hk1 hdT hd1
  rw [hval] at htE
  rw [gz_glZeta_eq (lt_of_lt_of_le hlim.bot_lt (le_add_self : d ≤ P + d)).ne' ?_, gz_lg_add _ hd0]
  obtain ⟨a, ha, hta⟩ := ((isNormal_veblen _).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 htE
  have hc'' : a - i0 < d := by
    rcases lt_or_ge a i0 with hai | hai
    · rw [Ordinal.sub_eq_zero_iff_le.2 hai.le]; exact hlim.bot_lt
    · have : i0 + (a - i0) < i0 + d := by rw [Ordinal.add_sub_cancel_of_le hai]; exact ha
      exact (add_lt_add_iff_left _).1 this
  refine ⟨P + (a - i0), (add_lt_add_iff_left _).2 hc'', ?_⟩
  have hd' : veblen ((k + 1 : ℕ) : Ordinal.{0}) (i0 + (a - i0)) < hbN (k + 1) P :=
    ((isNormal_veblen _).strictMono ((add_lt_add_iff_left _).2 hc'')).trans hd
  have hv : vt ρ (Om1 * ((k + 1 : ℕ) : Ordinal.{0}) + (P + (a - i0))) =
      veblen ((k + 1 : ℕ) : Ordinal.{0}) (i0 + (a - i0)) := (hb_step_cf h k hP0 hi0 hPq hHq hd').1
  rw [hv]
  exact hta.trans_le ((isNormal_veblen _).monotone (Ordinal.le_add_sub a i0))

omit h in
/-- Facts about the floor of `u` at level `k+1` inside `[N_k(P), N_{k+1}(P))`. -/
theorem hb_floor_step (k : ℕ) {P i0 u : Ordinal.{0}} (hi0 : veblen ((k + 1 : ℕ) : Ordinal.{0}) i0 = hbN k P)
    (hQu : hbN k P ≤ u) (huH : u < hbN (k + 1) P) :
    ∃ j, i0 ≤ j ∧ veblen ((k + 1 : ℕ) : Ordinal.{0}) j ≤ u ∧ u < veblen ((k + 1 : ℕ) : Ordinal.{0}) (j + 1) ∧
      veblen ((k + 1 : ℕ) : Ordinal.{0}) (j + 1) < hbN (k + 1) P := by
  obtain ⟨j, hj1, hj2⟩ := hb_floor ((k + 1 : ℕ) : Ordinal.{0}) (u := u) (j0 := i0) (by rw [hi0]; exact hQu)
  have hi0j : i0 ≤ j := by
    have : veblen ((k + 1 : ℕ) : Ordinal.{0}) i0 < veblen ((k + 1 : ℕ) : Ordinal.{0}) (j + 1) := by
      rw [hi0]; exact hQu.trans_lt hj2
    exact Order.lt_add_one_iff.1 ((isNormal_veblen _).strictMono.lt_iff_lt.1 this)
  have hH := hbN_fix (k + 1) P
  have hjH : j < hbN (k + 1) P := by
    have : veblen ((k + 1 : ℕ) : Ordinal.{0}) j < veblen ((k + 1 : ℕ) : Ordinal.{0}) (hbN (k + 1) P) := by
      rw [hH]; exact hj1.trans_lt huH
    exact (isNormal_veblen _).strictMono.lt_iff_lt.1 this
  have hj1H : j + 1 < hbN (k + 1) P := (ev_isSuccLimit_of_inE (hbN_E (k + 1) P)).add_one_lt hjH
  refine ⟨j, hi0j, hj1, hj2, ?_⟩
  have := (isNormal_veblen ((k + 1 : ℕ) : Ordinal.{0})).strictMono hj1H
  rwa [hH] at this

/-- **THE REACH TEST ON `[N_k(P), N_{k+1}(P))`** (given `HbDown k`): every `ε`-number there has Veblen level
`≤ k+1`. -/
theorem hb_downStep (k : ℕ) (HD : HbDown ρ k) {P i0 : Ordinal.{0}} (hP0 : glA ((k + 1 : ℕ) : Ordinal.{0}) P ρ = hbN k P)
    (hi0 : veblen ((k + 1 : ℕ) : Ordinal.{0}) i0 = hbN k P) (hρP : ρ < P) (hPq : P < gq 1 ρ)
    (hHq : hbN (k + 1) P < gq 1 ρ) {u : Ordinal.{0}} (hu : InE u) (hQu : hbN k P ≤ u) (huH : u < hbN (k + 1) P) :
    ∃ m : ℕ, ∃ ζ, m ≤ k + 1 ∧ IsLh1 u (u * ((m : Ordinal.{0}) + 1) + ζ) ∧ ζ < u := by
  obtain ⟨j, hi0j, hj1, hj2, hj1H⟩ := hb_floor_step k hi0 hQu huH
  have hρQ : ρ < hbN k P := hρP.trans (hbN_gt k P)
  rcases hj1.lt_or_eq with hju | hju
  · have hρj : ρ < veblen ((k + 1 : ℕ) : Ordinal.{0}) j :=
      hρQ.trans_le (by rw [← hi0]; exact (isNormal_veblen _).monotone hi0j)
    obtain ⟨m, ζ, hm, hl, hζ⟩ := HD _ u (hb_fix_veb k j) hρj (by rw [hbN_veb]; exact hj1H.trans hHq) hu hju
      (by rw [hbN_veb]; exact hj2)
    exact ⟨m, ζ, hm.trans (Nat.le_succ k), hl, hζ⟩
  · obtain ⟨d, rfl⟩ := exists_add_of_le hi0j
    obtain ⟨hL, hζ⟩ := hb_step_lh h k hP0 hi0 hρP hPq hHq (hju ▸ huH)
    rw [hju] at hL hζ
    exact ⟨k + 1, _, le_rfl, hL, hζ⟩

/-- **LEMMA IMG ON `[N_k(P), N_{k+1}(P))`** (given `HbDown k`, `HbNext k` and Lemma IMG up to `N_k(P)`). -/
theorem hb_imgStep (k : ℕ) (HD : HbDown ρ k) (HN : HbNext ρ δ k) {P i0 : Ordinal.{0}}
    (hP0 : glA ((k + 1 : ℕ) : Ordinal.{0}) P ρ = hbN k P)
    (hi0 : veblen ((k + 1 : ℕ) : Ordinal.{0}) i0 = hbN k P) (hρP : ρ < P) (hPq : P < gq 1 ρ)
    (hHq : hbN (k + 1) P < gq 1 ρ) (hle : ∀ v, v ≤ hbN k P → GnI ρ δ v) :
    ∀ v, v < hbN (k + 1) P → GnI ρ δ v := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hρQ : ρ < hbN k P := hρP.trans (hbN_gt k P)
  refine gnImg_of_eps h (fun v hv => gm1_T hρE hρ1 (hv.trans hHq)) (fun e he _ heB IHe => ?_)
  rcases le_or_gt e (hbN k P) with heQ | hQe
  · exact hle e heQ
  obtain ⟨j, hi0j, hj1, hj2, hj1H⟩ := hb_floor_step k hi0 hQe.le heB
  rcases hj1.lt_or_eq with hje | hje
  · -- `e` strictly between two points of level `k+1`: `HbNext k` over the pseudo-base `φ(k+1, j)`
    have hρj : ρ < veblen ((k + 1 : ℕ) : Ordinal.{0}) j :=
      hρQ.trans_le (by rw [← hi0]; exact (isNormal_veblen _).monotone hi0j)
    exact HN _ (hb_fix_veb k j) hρj (by rw [hbN_veb]; exact hj1H.trans hHq)
      (fun v hv => IHe v (hv.trans_lt hje)) e (by rw [hbN_veb]; exact hj2)
  · obtain ⟨d, rfl⟩ := exists_add_of_le hi0j
    have hdH : veblen ((k + 1 : ℕ) : Ordinal.{0}) (i0 + d) < hbN (k + 1) P := hje ▸ heB
    obtain ⟨hval, hdq⟩ := hb_step_cf h k hP0 hi0 hPq hHq hdH
    obtain ⟨hdT, hd1⟩ := gm1_T hρE hρ1 hdq
    have hn1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    rcases zero_or_succ_or_isSuccLimit d with h0 | ⟨d', hd'⟩ | hlim
    · subst h0
      rw [add_zero, hi0] at hje
      exact absurd hje hQe.ne
    · -- successor: `e = N_k(φ(k+1, i₀ + d'))`, the reach test with `E' = φ(k+1, i₀ + d')`
      have hd'' : d = d' + 1 := by rw [← hd', succ_eq_add_one]
      subst hd''
      set Q' := veblen ((k + 1 : ℕ) : Ordinal.{0}) (i0 + d') with hQ'
      have heN : e = hbN k Q' := by rw [← hje, ← add_assoc, hQ', hbN_veb]
      have hQ'e : Q' < e := by rw [heN]; exact hbN_gt k Q'
      have hρQ' : ρ < Q' := hρQ.trans_le (by rw [← hi0, hQ']; exact (isNormal_veblen _).monotone le_self_add)
      have he' : glA ((k + 1 : ℕ) : Ordinal.{0}) (P + (d' + 1)) ρ = e := by rw [hval]; exact hje
      have H := ha_img_down h (n := k + 1) hn1 hdT hd1 hρQ' (by rw [he']; exact hQ'e)
        (fun u hu hQ'u huE => by
          rw [he', heN] at huE
          obtain ⟨m, ζ, hm, hl, hζ⟩ := HD Q' u (hb_fix_veb k _) hρQ' (by rw [← heN]; exact heB.trans hHq) hu
            hQ'u huE
          exact ⟨m, ζ, hm.trans (Nat.le_succ k), hl, hζ, fun e => absurd e (by omega)⟩)
        (fun u hu => IHe u (by rw [he'] at hu; exact hu))
      rwa [he'] at H
    · -- limit: the reach test with `E' = φ(k+1, i₀ + c')`, `d = c' + ω^z`
      have hd0 : d ≠ 0 := hlim.bot_lt.ne'
      obtain ⟨c', hcs, hdvd, hc'd⟩ := lg_split hd0
      set z := lg d with hzdef
      set E' := veblen ((k + 1 : ℕ) : Ordinal.{0}) (i0 + c') with hE'def
      have hE'e : E' < e := by
        rw [← hje]; exact (isNormal_veblen _).strictMono ((add_lt_add_iff_left _).2 hc'd)
      have hρE' : ρ < E' := hρQ.trans_le (by rw [← hi0, hE'def]; exact (isNormal_veblen _).monotone le_self_add)
      have hz' : glZeta ρ (k + 1) (P + d) = z := hb_lev_glZeta h k hP0 hi0 hPq hHq hlim hdH
      have he' : glA ((k + 1 : ℕ) : Ordinal.{0}) (P + d) ρ = e := by rw [hval]; exact hje
      have H := ha_img_down h (n := k + 1) hn1 hdT hd1 hρE' (by rw [he']; exact hE'e) (fun u hu hE'u huE => ?_)
        (fun u hu => IHe u (by rw [he'] at hu; exact hu))
      · rwa [he'] at H
      rw [he'] at huE
      have huH : u < hbN (k + 1) P := huE.trans heB
      obtain ⟨j', hi0j', hj1', hj2', hj1H'⟩ := hb_floor_step k hi0
        (hρQ.le.trans' (le_refl _) |>.trans' le_rfl |> fun _ => (by
          rw [← hi0]; exact ((isNormal_veblen _).monotone le_self_add).trans hE'u.le)) huH
      have hcj : i0 + c' ≤ j' := by
        have : veblen ((k + 1 : ℕ) : Ordinal.{0}) (i0 + c') < veblen ((k + 1 : ℕ) : Ordinal.{0}) (j' + 1) :=
          hE'u.trans hj2'
        exact Order.lt_add_one_iff.1 ((isNormal_veblen _).strictMono.lt_iff_lt.1 this)
      have hjE : j' < i0 + d := by
        have : veblen ((k + 1 : ℕ) : Ordinal.{0}) j' < veblen ((k + 1 : ℕ) : Ordinal.{0}) (i0 + d) := by
          rw [hje]; exact hj1'.trans_lt huE
        exact (isNormal_veblen _).strictMono.lt_iff_lt.1 this
      rcases hj1'.lt_or_eq with hju | hju
      · have hρj : ρ < veblen ((k + 1 : ℕ) : Ordinal.{0}) j' :=
          hρE'.trans_le ((isNormal_veblen _).monotone hcj)
        obtain ⟨m, ζ, hm, hl, hζ⟩ := HD _ u (hb_fix_veb k j') hρj (by rw [hbN_veb]; exact hj1H'.trans hHq) hu hju
          (by rw [hbN_veb]; exact hj2')
        exact ⟨m, ζ, hm.trans (Nat.le_succ k), hl, hζ, fun e => absurd e (by omega)⟩
      · obtain ⟨d'', rfl⟩ := exists_add_of_le hi0j'
        have hc'd'' : c' < d'' := by
          rcases ((add_le_add_iff_left _).1 hcj).lt_or_eq with h' | h'
          · exact h'
          · exfalso; rw [← h'] at hju; exact absurd hju hE'u.ne
        have hd''d : d'' < d := (add_lt_add_iff_left _).1 hjE
        have hd''0 : d'' ≠ 0 := (lt_of_le_of_lt zero_le hc'd'').ne'
        obtain ⟨hL, hζu⟩ := hb_step_lh h k hP0 hi0 hρP hPq hHq (hju ▸ huH)
        rw [hju] at hL hζu
        have hζlg : glZeta ρ (k + 1) (P + d'') ≤ lg d'' :=
          (gz_glZeta_le ρ (P + d'') (k + 1)).trans (gz_lg_add _ hd''0).le
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
          exact absurd (h1.trans h2) (not_le.2 hδlt)
        refine ⟨k + 1, glZeta ρ (k + 1) (P + d''), le_rfl, ?_, hζu, fun _ => ?_⟩
        · exact hL
        · rw [hz']; exact hζlg.trans_lt hlgd

end Steps

/-! ## The induction on the level -/

section Ind

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

omit h in
theorem hb_two_cast : ((2 : ℕ) : Ordinal.{0}) = 2 := by norm_num

theorem hb_down_two : HbDown ρ 2 := by
  intro P u hP hρP hNq hu hPu huN
  rw [hb_two_cast] at hP
  rw [hbN2_eq] at hNq huN
  obtain ⟨m, ζ, hm, hl, hζ⟩ := ha_down_Pall h hP hρP hNq hu hPu huN
  exact ⟨m, ζ, hm, hl, hζ⟩

theorem hb_next_two : HbNext ρ δ 2 := by
  intro P hP hρP hNq hle v hv
  rw [hb_two_cast] at hP
  rw [hbN2_eq] at hNq hv
  exact ha_img_next h hP hρP hNq hle v hv

theorem hb_fixP_data (k : ℕ) {P : Ordinal.{0}} (hP : veblen ((k + 1 : ℕ) : Ordinal.{0}) P = P) (hρP : ρ < P)
    (hHq : hbN (k + 1) P < gq 1 ρ) :
    P < gq 1 ρ ∧ hbN k P ≤ hbN (k + 1) P ∧ glA ((k + 1 : ℕ) : Ordinal.{0}) P ρ = hbN k P ∧
      veblen (k : Ordinal.{0}) P = P := by
  have hPq : P < gq 1 ρ := (hbN_gt (k + 1) P).trans hHq
  refine ⟨hPq, hbN_le k (hb_fix_down (Nat.le_succ k) (hbN_fix (k + 1) P)) (hbN_gt (k + 1) P),
    hb_glA_fixP h.ρE h.ρ1 k hP hρP hPq, hb_fix_down (Nat.le_succ k) hP⟩

/-- **THE INDUCTION ON THE VEBLEN LEVEL**: `HbDown k` and `HbNext k` for every `k ≥ 2`. -/
theorem hb_DI : ∀ k : ℕ, 2 ≤ k → HbDown ρ k ∧ HbNext ρ δ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact ⟨hb_down_two h, hb_next_two h⟩
  | succ k hk IH =>
    obtain ⟨HD, HN⟩ := IH
    refine ⟨fun P u hP hρP hHq hu hPu huH => ?_, fun P hP hρP hHq hle v hv => ?_⟩
    · obtain ⟨hPq, hQH, hP0, hPk⟩ := hb_fixP_data h k hP hρP hHq
      obtain ⟨i0, hi0⟩ := hb_LuP_of_fix k (hbN_fix k P)
      rcases lt_or_ge u (hbN k P) with huQ | hQu
      · obtain ⟨m, ζ, hm, hl, hζ⟩ := HD P u hPk hρP (hQH.trans_lt hHq) hu hPu huQ
        exact ⟨m, ζ, hm.trans (Nat.le_succ k), hl, hζ⟩
      · exact hb_downStep h k HD hP0 hi0 hρP hPq hHq hu hQu huH
    · obtain ⟨hPq, hQH, hP0, hPk⟩ := hb_fixP_data h k hP hρP hHq
      obtain ⟨i0, hi0⟩ := hb_LuP_of_fix k (hbN_fix k P)
      have hQq : hbN k P < gq 1 ρ := hQH.trans_lt hHq
      have hbelow : ∀ v, v < hbN k P → GnI ρ δ v := HN P hPk hρP hQq hle
      -- Lemma IMG at `N_k(P) = ϑᵖ(Ω₁·(k+1) + P)`: the reach test going down with `E' = P`
      have hatQ : GnI ρ δ (hbN k P) := by
        obtain ⟨hPT, hP1⟩ := gm1_T h.ρE h.ρ1 hPq
        have H := ha_img_down h (n := k + 1) (Nat.succ_le_succ (Nat.zero_le k)) hPT hP1 hρP
          (by rw [hP0]; exact hbN_gt k P)
          (fun u hu hPu huQ => by
            rw [hP0] at huQ
            obtain ⟨m, ζ, hm, hl, hζ⟩ := HD P u hPk hρP hQq hu hPu huQ
            exact ⟨m, ζ, hm.trans (Nat.le_succ k), hl, hζ, fun e => absurd e (by omega)⟩)
          (fun u hu => hbelow u (by rw [hP0] at hu; exact hu))
        rwa [hP0] at H
      exact hb_imgStep h k HD HN hP0 hi0 hρP hPq hHq
        (fun v hv => (hv.lt_or_eq).elim (hbelow v) (fun e => e ▸ hatQ)) v hv

theorem hb_down {k : ℕ} (hk : 2 ≤ k) : HbDown ρ k := (hb_DI h k hk).1

theorem hb_img_next {k : ℕ} (hk : 2 ≤ k) : HbNext ρ δ k := (hb_DI h k hk).2

end Ind

/-! ## Lemma IMG below `B_{k+1}(ρ) = N_k(Γ_{ρ+1})` -/

section Bk

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`N_k(Γ_{x+1}) < Γ_{x+2}`** for every `k`. -/
theorem hbN_G_lt (k : ℕ) : hbN k (lgG x) < gq 1 x := by
  have hq := (gm1_facts hx hx1).2.2.2
  obtain ⟨hkT, hk1⟩ := hb_lev_T hx hx1 (k + 1)
  obtain ⟨hGT, -, hG1, -, -⟩ := lgG_facts hx hx1
  rw [← hb_glA_G hx hx1 k]
  exact lgVt_lt_low hx hx1 hkT hk1 hGT hG1 (gm1_one_T hx hx1).1 (gm1_one_T hx hx1).2
    ((natCast_lt_omega0 _).trans (omega0_lt_inE hq)) (mg_lgG_lt_G1 hx hx1)

/-- **`N_3(Γ_{x+1}) = B₄(x)`.** -/
theorem hb_N3_eq : hbN 3 (lgG x) = haB4 x := by
  have e3 : ((3 : ℕ) : Ordinal.{0}) = 3 := by norm_num
  refine le_antisymm ?_ ?_
  · refine hbN_le 3 (by rw [e3]; exact haB4_fix x) ?_
    exact ((lgG_facts hx hx1).2.1.trans_le (le_refl _) |> fun _ =>
      ((lt_evZ _).trans (gzZ1_lt_B3 x)).trans (haB3_lt_B4 x))
  · refine ha_fix_ge_B4 (by have := hbN_fix 3 (lgG x); rwa [e3] at this) ?_
    have hB3 : gzB3 x = hbN 2 (lgG x) := by rw [hbN2_eq]; rfl
    have hle : hbN 2 (lgG x) ≤ hbN 3 (lgG x) :=
      hbN_le 2 (hb_fix_down (by norm_num) (hbN_fix 3 (lgG x))) (hbN_gt 3 (lgG x))
    rw [hB3]
    refine lt_of_le_of_ne hle fun e => ?_
    have h3 : veblen 3 (gzB3 x) = gzB3 x := by
      have := hbN_fix 3 (lgG x); rw [e3, ← e, ← hB3] at this; exact this
    exact ha_B3_notfix3 hx hx1 h3

end Bk

section ImgB

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG UP TO `B_{k+1}(ρ) = N_k(Γ_{ρ+1})`, FOR EVERY `k ≥ 2`** (`k = 2`: `B₃(ρ)`, `Ha.ha_img_le_B3`; the step
by `hb_imgStep` over the pseudo-base `Γ_{ρ+1}` and the reach test at `N_{k+1}(Γ_{ρ+1})` with `E' = N_k(Γ_{ρ+1})`). -/
theorem hb_img_le_B : ∀ k : ℕ, 2 ≤ k → ∀ v, v ≤ hbN k (lgG ρ) → GnI ρ δ v := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro v hv
    rw [hbN2_eq] at hv
    exact ha_img_le_B3 h hv
  | succ k hk IH =>
    have hρE := h.ρE
    have hρ1 := h.ρ1
    obtain ⟨HD, HN⟩ := hb_DI h k hk
    obtain ⟨hGT, hρG, hG1, -, -⟩ := lgG_facts hρE hρ1
    have hGq : lgG ρ < gq 1 ρ := mg_lgG_lt_G1 hρE hρ1
    have hHq := hbN_G_lt hρE hρ1 (k + 1)
    have hP0 := hb_glA_G hρE hρ1 k
    obtain ⟨i0, hi0⟩ := hb_LuP_of_fix k (hbN_fix k (lgG ρ))
    have hbelow := hb_imgStep h k HD HN hP0 hi0 hρG hGq hHq IH
    have hQH : hbN k (lgG ρ) < hbN (k + 1) (lgG ρ) := by
      rw [← hP0, ← hb_glA_G hρE hρ1 (k + 1)]
      obtain ⟨hkT, hk1⟩ := hb_lev_T hρE hρ1 (k + 2)
      have hlev : ((k + 1 : ℕ) : Ordinal.{0}) < ((k + 2 : ℕ) : Ordinal.{0}) := hb_nat_lt (Nat.lt_succ_self _)
      exact (glA_lev hρE hρ1 (hb_one_le k) hlev hkT hk1 hGT hG1 hGT hG1).2
        (glA_facts hρE hρ1 (hb_one_le (k + 1)) hkT hk1 hGT hG1).2.2.2.2.2
    -- Lemma IMG at `N_{k+1}(Γ_{ρ+1}) = ϑᵖ(Ω₁·(k+2) + Γ_{ρ+1})`
    have hP1 := hb_glA_G hρE hρ1 (k + 1)
    have hat : GnI ρ δ (hbN (k + 1) (lgG ρ)) := by
      have H := ha_img_down h (n := k + 2) (by omega) hGT hG1 (hρG.trans (hbN_gt k _))
        (by rw [hP1]; exact hQH)
        (fun u hu hQu huH => by
          rw [hP1] at huH
          obtain ⟨m, ζ, hm, hl, hζ⟩ := hb_downStep h k HD hP0 hi0 hρG hGq hHq hu hQu.le huH
          exact ⟨m, ζ, hm.trans (Nat.le_succ _), hl, hζ, fun e => absurd e (by omega)⟩)
        (fun u hu => hbelow u (by rw [hP1] at hu; exact hu))
      rwa [hP1] at H
    intro v hv
    rcases hv.lt_or_eq with hlt | heq
    · exact hbelow v hlt
    · rw [heq]; exact hat

/-- **LEMMA IMG BELOW `B_{k+1}(ρ) = N_k(Γ_{ρ+1})` FOR EVERY `k`.** -/
theorem hb_img_B (k : ℕ) : ∀ v, v < hbN k (lgG ρ) → GnI ρ δ v := by
  intro v hv
  have hk : hbN k (lgG ρ) ≤ hbN (k + 2) (lgG ρ) :=
    hbN_le k (hb_fix_down (by omega) (hbN_fix (k + 2) (lgG ρ))) (hbN_gt (k + 2) (lgG ρ))
  exact hb_img_le_B h (k + 2) (by omega) v (hv.le.trans hk)

end ImgB

/-- **`B_ω(x) = sup_k N_k(Γ_{x+1})`.** -/
noncomputable def hbBw (x : Ordinal.{0}) : Ordinal.{0} := ⨆ k : ℕ, hbN k (lgG x)

section ImgBw

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

omit h in
theorem hbBw_bdd (x : Ordinal.{0}) : BddAbove (Set.range fun k : ℕ => hbN k (lgG x)) :=
  Ordinal.bddAbove_range _

omit h in
theorem hbN_le_Bw (k : ℕ) (x : Ordinal.{0}) : hbN k (lgG x) ≤ hbBw x :=
  le_ciSup (hbBw_bdd x) k

omit h in
theorem hbN_lt_Bw (k : ℕ) (x : Ordinal.{0}) : hbN k (lgG x) < hbBw x :=
  (hbN_lt_succ k _).trans_le (hbN_le_Bw (k + 1) x)

/-- **LEMMA IMG BELOW `B_ω(ρ)`.** -/
theorem hb_img_Bw : ∀ v, v < hbBw ρ → GnI ρ δ v := by
  intro v hv
  obtain ⟨k, hk⟩ := (lt_ciSup_iff (hbBw_bdd ρ)).1 hv
  exact hb_img_B h k v hk

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW `B_{k+1}(ρ)`, EVERY `k`.** -/
theorem hb_pkg_B (k : ℕ) {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : T ρ < hbN k (lgG ρ)) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (hb_img_B h k _ hT) hex

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW `B_ω(ρ)`.** -/
theorem hb_pkg_Bw {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : T ρ < hbBw ρ) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (hb_img_Bw h _ hT) hex

end ImgBw

/-! ## The bound `B_ω(x)` -/

section BwBase

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`B_ω(x) ≤ ϑˣ(Ω₁·ω + Γ_{x+1})`**, a common fixed point of every `φ(k, ·)` above `Γ_{x+1}`. -/
theorem hbBw_le_glA : hbBw x ≤ glA ω (lgG x) x := by
  have hq := (gm1_facts hx hx1).2.2.2
  obtain ⟨hωT, hω1⟩ := gm1_T hx hx1 (omega0_lt_inE hq)
  obtain ⟨hGT, -, hG1, -, -⟩ := lgG_facts hx hx1
  have hW := glA_P hx hx1 (one_lt_omega0.le) hωT hω1 hGT hG1
  obtain ⟨-, -, -, -, -, hGW⟩ := glA_facts hx hx1 one_lt_omega0.le hωT hω1 hGT hG1
  refine ciSup_le fun k => hbN_le k ?_ hGW
  exact (mem_range_veblen omega0_ne_zero).1 hW _ (natCast_lt_omega0 k)

/-- **`B_ω(x) < Γ_{x+2}`.** -/
theorem hbBw_lt1 : hbBw x < gq 1 x := by
  have hq := (gm1_facts hx hx1).2.2.2
  obtain ⟨hωT, hω1⟩ := gm1_T hx hx1 (omega0_lt_inE hq)
  obtain ⟨hGT, -, hG1, -, -⟩ := lgG_facts hx hx1
  exact (hbBw_le_glA hx hx1).trans_lt (lgVt_lt_low hx hx1 hωT hω1 hGT hG1 (gm1_one_T hx hx1).1
    (gm1_one_T hx hx1).2 (omega0_lt_inE hq) (mg_lgG_lt_G1 hx hx1))

omit hx hx1 in
theorem hb_B3_le_Bw : gzB3 x ≤ hbBw x := by
  have e : gzB3 x = hbN 2 (lgG x) := by rw [hbN2_eq]; rfl
  rw [e]; exact hbN_le_Bw 2 x

/-- **`B₄(x) ≤ B_ω(x)`.** -/
theorem hb_B4_le_Bw : haB4 x ≤ hbBw x := by
  rw [← hb_N3_eq hx hx1]; exact hbN_le_Bw 3 x

end BwBase

/-- **`B_ω(x)` is a fixed point of every `φ(k, ·)`, `k < ω`.** -/
theorem hbBw_veb (k : ℕ) (x : Ordinal.{0}) : veblen (k : Ordinal.{0}) (hbBw x) = hbBw x := by
  unfold hbBw
  rw [(isNormal_veblen (k : Ordinal.{0})).map_iSup (hbBw_bdd x)]
  refine le_antisymm (Ordinal.iSup_le fun n => ?_) (Ordinal.iSup_le fun n => ?_)
  · have h1 : veblen (k : Ordinal.{0}) (hbN n (lgG x)) ≤ veblen (k : Ordinal.{0}) (hbN (n + k) (lgG x)) :=
      (isNormal_veblen _).monotone (hbN_mono (Nat.le_add_right n k) _)
    rw [hb_fix_down (Nat.le_add_left k n) (hbN_fix (n + k) (lgG x))] at h1
    exact h1.trans (Ordinal.le_iSup (fun n => hbN n (lgG x)) (n + k))
  · exact (right_le_veblen _ _).trans (Ordinal.le_iSup (fun n => veblen (k : Ordinal.{0}) (hbN n (lgG x))) n)

end Googology.Trans.PoR.InaccPsi.R2.Hb
