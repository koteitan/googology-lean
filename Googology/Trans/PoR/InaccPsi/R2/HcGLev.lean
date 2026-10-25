import Googology.Trans.PoR.InaccPsi.R2.HcImg

/-!
# HcGLev: THE LEVEL FACTS AT EVERY ORDINAL VEBLEN LEVEL `α`

`Hb.HbLev` and `Hc.HcLev` state the interval structure over a pseudo-base for the finite levels and for `ω`.  Here
the level is any ordinal `α` (successor or limit):

* `hcN α Q` (**the least fixed point of `φ(α, ·)` above `Q`**), `hcN_fix`, `hcN_gt`, `hcN_le`, `hcN_E`, `hc_fix_down`,
  `hc_LuP_of_fix`, `hc_fix_of_LuP`, `hcN_mono`, `hcN_veb` (`N_γ(φ(γ+1, a)) = φ(γ+1, a+1)`);
* `hc_gap` (**THE GAP LEMMA**: every ordinal strictly between two consecutive points `φ(α, j) < φ(α, j+1)` lies below
  `N_γ(φ(α, j))` for some `γ < α`; successor `α` by `hcN_veb`, limit `α` by the supremum of the `N_γ`, which is a
  common fixed point of every `φ(γ, ·)`, `γ < α`), `hc_floorG`, `hc_nofixG`;
* at an `ε`-number base `x`: `hc_lowG`, `hc_glA_fixG` (**`ϑˣ(Ω₁·α + P) = φ(α, P+1)`** at a fixed point `P` of
  `φ(α, ·)`), `hc_glA_GG` (at `P = Γ_{x+1}`), `hc_zetaG` (`ζ = logend(d)` at a limit `d`), `hc_luL_lt`
  (**`luL(a, q) = a·(1+q)` for `1 ≤ q < ω^ω`**), `hc_lhG` (**THE REACH AT EVERY LEVEL `1 ≤ q < ω^ω`**:
  `lh(ϑˣ(Ω₁·q + t)) = ϑˣ(Ω₁·q + t)·(1+q) + ζ`), `hcN_G_lt` (`N_α(Γ_{x+1}) < Γ_{x+2}` for `α < Γ_{x+2}`).

No new axiom.  New definition: `hcN`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hc

open Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The next fixed point at every level -/

/-- **The least fixed point of `φ(α, ·)` above `Q`.** -/
noncomputable def hcN (α Q : Ordinal.{0}) : Ordinal.{0} := nfp (veblen α) (Q + 1)

theorem hcN_fix (α Q : Ordinal.{0}) : veblen α (hcN α Q) = hcN α Q := nfp_fp (isNormal_veblen _) _

theorem hcN_gt (α Q : Ordinal.{0}) : Q < hcN α Q := (lt_add_one Q).trans_le (le_nfp _ _)

theorem hcN_le {α Q j : Ordinal.{0}} (hj : veblen α j = j) (hQj : Q < j) : hcN α Q ≤ j :=
  nfp_le_fp (isNormal_veblen _).strictMono.monotone (Order.add_one_le_of_lt hQj) hj.le

/-- **A fixed point of `φ(α, ·)` is a fixed point of every `φ(γ, ·)`, `γ ≤ α`.** -/
theorem hc_fix_down {γ α P : Ordinal.{0}} (hγα : γ ≤ α) (hP : veblen α P = P) : veblen γ P = P := by
  rcases hγα.lt_or_eq with h | rfl
  · have := veblen_veblen_of_lt h P; rwa [hP] at this
  · exact hP

theorem hc_fix_E {α P : Ordinal.{0}} (hP : veblen α P = P) : InE P := by
  have h := hc_fix_down zero_le hP; rw [veblen_zero_apply] at h; exact h

theorem hcN_E (α Q : Ordinal.{0}) : InE (hcN α Q) := hc_fix_E (hcN_fix α Q)

theorem hcN_lim (α Q : Ordinal.{0}) : IsSuccLimit (hcN α Q) := ev_isSuccLimit_of_inE (hcN_E α Q)

theorem hc_LuP_of_fix {γ P : Ordinal.{0}} (hP : veblen γ P = P) : LuP (γ + 1) P := by
  unfold LuP
  rw [mem_range_veblen (by simp)]
  intro b hb
  exact hc_fix_down (Order.lt_add_one_iff.1 hb) hP

theorem hc_fix_of_LuP {γ P : Ordinal.{0}} (h : LuP (γ + 1) P) : veblen γ P = P := by
  obtain ⟨a, rfl⟩ := h
  exact veblen_veblen_of_lt (lt_add_one γ) a

/-- **`N_γ(Q) ≤ N_α(Q)`** for `γ ≤ α`. -/
theorem hcN_mono {γ α : Ordinal.{0}} (hγα : γ ≤ α) (Q : Ordinal.{0}) : hcN γ Q ≤ hcN α Q :=
  hcN_le (hc_fix_down hγα (hcN_fix α Q)) (hcN_gt α Q)

theorem hcN_nat (k : ℕ) (Q : Ordinal.{0}) : hcN (k : Ordinal.{0}) Q = hbN k Q := rfl

theorem hcN_om (Q : Ordinal.{0}) : hcN ω Q = hcNw Q := rfl

/-- **`N_γ(φ(γ+1, a)) = φ(γ+1, a+1)`.** -/
theorem hcN_veb (γ a : Ordinal.{0}) : hcN γ (veblen (γ + 1) a) = veblen (γ + 1) (a + 1) := by
  have hlt : veblen (γ + 1) a < veblen (γ + 1) (a + 1) := (isNormal_veblen _).strictMono (lt_add_one a)
  refine le_antisymm (hcN_le (veblen_veblen_of_lt (lt_add_one γ) (a + 1)) hlt) ?_
  obtain ⟨b, hb⟩ := hc_LuP_of_fix (hcN_fix γ (veblen (γ + 1) a))
  have hab : veblen (γ + 1) a < veblen (γ + 1) b := by rw [hb]; exact hcN_gt γ _
  rw [← hb]
  exact (isNormal_veblen _).monotone (Order.add_one_le_of_lt ((isNormal_veblen _).strictMono.lt_iff_lt.1 hab))

/-! ## The gap lemma -/

/-- **THE GAP LEMMA**: an ordinal strictly between two consecutive points `φ(α, j) < φ(α, j+1)` (`α ≠ 0`) lies below
`N_γ(φ(α, j))` for some `γ < α`. -/
theorem hc_gap {α j u : Ordinal.{0}} (hα : α ≠ 0) (hju : veblen α j < u) (huj : u < veblen α (j + 1)) :
    ∃ γ, γ < α ∧ u < hcN γ (veblen α j) := by
  by_contra hne
  push Not at hne
  set Q := veblen α j with hQ
  -- a point of `range φ(α, ·)` in `(Q, u]` contradicts `u < φ(α, j+1)`
  have key : ∀ v, LuP α v → Q < v → v ≤ u → False := by
    rintro v ⟨i, rfl⟩ hQv hvu
    have hji : j < i := (isNormal_veblen _).strictMono.lt_iff_lt.1 hQv
    have := (isNormal_veblen α).monotone (Order.add_one_le_of_lt hji)
    exact absurd (huj.trans_le this) (not_lt.2 hvu)
  rcases zero_or_succ_or_isSuccLimit α with h0 | ⟨γ, hγ⟩ | hlim
  · exact hα h0
  · have hγ' : α = γ + 1 := by rw [← hγ, succ_eq_add_one]
    subst hγ'
    exact key _ (hc_LuP_of_fix (hcN_fix γ Q)) (hcN_gt γ Q) (hne γ (lt_add_one γ))
  · haveI : Nonempty (Iio α) := ⟨⟨0, hlim.bot_lt⟩⟩
    set v := ⨆ γ : Iio α, hcN γ.1 Q with hv
    have hbdd : BddAbove (Set.range fun γ : Iio α => hcN γ.1 Q) := Ordinal.bddAbove_of_small
    have hle : ∀ γ : Iio α, hcN γ.1 Q ≤ v := fun γ => le_ciSup hbdd γ
    have hfix : ∀ b, b < α → veblen b v = v := by
      intro b hb
      rw [hv, (isNormal_veblen b).map_iSup hbdd]
      refine le_antisymm (Ordinal.iSup_le fun γ => ?_) (Ordinal.iSup_le fun γ => ?_)
      · rcases le_or_gt b γ.1 with hbγ | hγb
        · rw [hc_fix_down hbγ (hcN_fix γ.1 Q)]; exact hle γ
        · have h1 : veblen b (hcN γ.1 Q) ≤ veblen b (hcN b Q) := (isNormal_veblen b).monotone (hcN_mono hγb.le Q)
          rw [hcN_fix] at h1
          exact h1.trans (hle ⟨b, hb⟩)
      · exact (right_le_veblen _ _).trans (Ordinal.le_iSup (fun γ : Iio α => veblen b (hcN γ.1 Q)) γ)
    have hvP : LuP α v := (mem_range_veblen hα).2 hfix
    have hQv : Q < v := (hcN_gt 0 Q).trans_le (hle ⟨0, hlim.bot_lt⟩)
    exact key v hvP hQv (Ordinal.iSup_le fun γ => hne γ.1 γ.2)

/-- Every ordinal in `[φ(α, P+1), N_α(P))` lies in some `[φ(α, j), φ(α, j+1))` with `P + 1 ≤ j`. -/
theorem hc_floorG {α P u : Ordinal.{0}} (hP : veblen α P = P) (hSu : veblen α (P + 1) ≤ u) (huN : u < hcN α P) :
    ∃ j, P + 1 ≤ j ∧ veblen α j ≤ u ∧ u < veblen α (j + 1) ∧ veblen α (j + 1) < hcN α P := by
  obtain ⟨j, hj1, hj2⟩ := hb_floor α (u := u) (j0 := P + 1) hSu
  have hi0j : P + 1 ≤ j := by
    have : veblen α (P + 1) < veblen α (j + 1) := hSu.trans_lt hj2
    exact Order.lt_add_one_iff.1 ((isNormal_veblen _).strictMono.lt_iff_lt.1 this)
  have hH := hcN_fix α P
  have hjH : j < hcN α P := by
    have : veblen α j < veblen α (hcN α P) := by rw [hH]; exact hj1.trans_lt huN
    exact (isNormal_veblen _).strictMono.lt_iff_lt.1 this
  have hj1H : j + 1 < hcN α P := (hcN_lim α P).add_one_lt hjH
  refine ⟨j, hi0j, hj1, hj2, ?_⟩
  have := (isNormal_veblen α).strictMono hj1H
  rwa [hH] at this

/-- **No fixed point of `φ(α, ·)` in `[i, N_α(P))`** when `P < φ(α, i)`. -/
theorem hc_nofixG {α P i j : Ordinal.{0}} (hi : P < veblen α i) (hij : i ≤ j) (hjB : veblen α j < hcN α P) :
    j < veblen α j := by
  rcases (right_le_veblen α j).lt_or_eq with h | h
  · exact h
  · exfalso
    have hPj : P < j := by
      have h1 : veblen α i ≤ veblen α j := (isNormal_veblen _).monotone hij
      rw [← h] at h1
      exact hi.trans_le h1
    exact absurd hjB (not_lt.2 ((hcN_le h.symm hPj).trans h.le))

/-- `φ(α, P) < φ(α, P+1)` and `P < φ(α, P+1)` at a fixed point `P`. -/
theorem hc_lt_next {α P : Ordinal.{0}} (hP : veblen α P = P) : P < veblen α (P + 1) := by
  have := (isNormal_veblen α).strictMono (lt_add_one P); rwa [hP] at this

/-- `φ(α, P+1) < N_α(P)` at a fixed point `P` of `φ(α, ·)`. -/
theorem hc_next_lt_N {α P : Ordinal.{0}} : veblen α (P + 1) < hcN α P := by
  have h := (isNormal_veblen α).strictMono ((hcN_lim α P).add_one_lt (hcN_gt α P))
  rwa [hcN_fix] at h

/-- `ω^ω < e` for every `ε`-number `e`. -/
theorem hc_ww_lt_E {e : Ordinal.{0}} (he : InE e) : ω ^ ω < e :=
  ((opow_lt_opow_iff_right one_lt_omega0).2 (omega0_lt_inE he)).trans_eq he

/-! ## The points of level `α` at an `ε`-number base -/

section BaseG

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- `ϑˣ(Ω₁·α + σ) < P` for every `σ < P`, `P ∈ (x, Γ_{x+2})` a fixed point of `φ(α, ·)`, `α < P`. -/
theorem hc_lowG {α P : Ordinal.{0}} (hα1 : 1 ≤ α) (hαq : α < gq 1 x) (hP : veblen α P = P) (hαP : α < P)
    (hxP : x < P) (hPq : P < gq 1 x) : ∀ σ, σ < P → glA α σ x < P := by
  obtain ⟨hαT, hαΩ⟩ := gm1_T hx hx1 hαq
  have hP2 : LuP α P := ⟨P, hP⟩
  have hP3 : LuP (α + 1) P := hc_LuP_of_fix hP
  intro σ
  induction σ using WellFoundedLT.induction with
  | ind σ IH =>
  intro hσ
  obtain ⟨hσT, hσ1⟩ := gm1_T hx hx1 (hσ.trans hPq)
  have hle : glA α σ x ≤ P := glA_min hx hx1 hα1 hαT hαΩ hσT hσ1 hP2 hxP hσ hαP
    (fun σ' h' => IH σ' h' (h'.trans hσ))
  exact lt_of_le_of_ne hle (fun e => glA_notP hx hx1 hα1 hαT hαΩ hσT hσ1 (by rw [e]; exact hP3))

/-- **`ϑˣ(Ω₁·α + P) = φ(α, P + 1)`** when every `ϑˣ(Ω₁·α + σ)`, `σ < P`, lies below `P` (`P` a fixed point). -/
theorem hc_glA_baseG {α P : Ordinal.{0}} (hα1 : 1 ≤ α) (hαq : α < gq 1 x) (hP : veblen α P = P) (hαP : α < P)
    (hlow : ∀ σ, σ < P → glA α σ x < P) (hxP : x < P) (hPq : P < gq 1 x) : glA α P x = veblen α (P + 1) := by
  obtain ⟨hαT, hαΩ⟩ := gm1_T hx hx1 hαq
  obtain ⟨hPT, hP1⟩ := gm1_T hx hx1 hPq
  have hPS : P < veblen α (P + 1) := hc_lt_next hP
  refine le_antisymm ?_ ?_
  · exact glA_min hx hx1 hα1 hαT hαΩ hPT hP1 ⟨_, rfl⟩ (hxP.trans hPS) hPS (hαP.trans hPS)
      (fun σ hσ => (hlow σ hσ).trans hPS)
  · obtain ⟨-, -, -, -, -, hta⟩ := glA_facts hx hx1 hα1 hαT hαΩ hPT hP1
    obtain ⟨i, hi⟩ := glA_P hx hx1 hα1 hαT hαΩ hPT hP1
    rw [← hi] at hta ⊢
    conv_lhs at hta => rw [← hP]
    exact (isNormal_veblen α).monotone (Order.add_one_le_of_lt ((isNormal_veblen α).strictMono.lt_iff_lt.1 hta))

/-- **`ϑˣ(Ω₁·α + P) = φ(α, P + 1)`** at a fixed point `P ∈ (x, Γ_{x+2})` of `φ(α, ·)` with `α < P`. -/
theorem hc_glA_fixG {α P : Ordinal.{0}} (hα1 : 1 ≤ α) (hαq : α < gq 1 x) (hP : veblen α P = P) (hαP : α < P)
    (hxP : x < P) (hPq : P < gq 1 x) : glA α P x = veblen α (P + 1) :=
  hc_glA_baseG hx hx1 hα1 hαq hP hαP (hc_lowG hx hx1 hα1 hαq hP hαP hxP hPq) hxP hPq

/-- **`ϑˣ(Ω₁·α + Γ_{x+1}) = φ(α, Γ_{x+1} + 1)`** for `1 ≤ α < Γ_{x+1}`. -/
theorem hc_glA_GG {α : Ordinal.{0}} (hα1 : 1 ≤ α) (hαG : α < lgG x) :
    glA α (lgG x) x = veblen α (lgG x + 1) := by
  obtain ⟨-, hxG, -, -, -⟩ := lgG_facts hx hx1
  have hGq := mg_lgG_lt_G1 hx hx1
  exact hc_glA_fixG hx hx1 hα1 (hαG.trans hGq) (hc_G_fix hx hx1 hα1 hαG) hαG hxG hGq

/-- **`ζ = logend(d)`** for the point `ϑˣ(Ω₁·α + P + d) = φ(α, i + d)` at a limit `d`. -/
theorem hc_zetaG {α P i d : Ordinal.{0}} (hα1 : 1 ≤ α) (hαq : α < gq 1 x) (hPq : P < gq 1 x)
    (hG0 : glA α P x = veblen α i) (hdq : P + d < gq 1 x)
    (hfix : ∀ ν', ν' ≤ d → IsSuccLimit ν' → i + ν' < veblen α (i + ν')) (hlim : IsSuccLimit d) :
    luZeta x α (P + d) = lg d := by
  classical
  have hd0 : d ≠ 0 := hlim.bot_lt.ne'
  obtain ⟨hαT, hαΩ⟩ := gm1_T hx hx1 hαq
  have hval := hc_glAV hx hx1 hα1 hαq hPq hG0 d hdq hfix
  obtain ⟨hdT, hd1⟩ := gm1_T hx hx1 hdq
  obtain ⟨-, -, -, -, -, htE⟩ := glA_facts hx hx1 hα1 hαT hαΩ hdT hd1
  rw [hval] at htE
  obtain ⟨a, ha, hta⟩ := ((isNormal_veblen _).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 htE
  have hc'' : a - i < d := by
    rcases lt_or_ge a i with hai | hai
    · rw [Ordinal.sub_eq_zero_iff_le.2 hai.le]; exact hlim.bot_lt
    · have : i + (a - i) < i + d := by rw [Ordinal.add_sub_cancel_of_le hai]; exact ha
      exact (add_lt_add_iff_left _).1 this
  have hq' : P + (a - i) < gq 1 x := ((add_lt_add_iff_left _).2 hc'').trans hdq
  have hv' : glA α (P + (a - i)) x = veblen α (i + (a - i)) :=
    hc_glAV hx hx1 hα1 hαq hPq hG0 (a - i) hq' (fun ν' h' hl => hfix ν' (h'.trans hc''.le) hl)
  have hcond : P + d < vt x (Om1 * α + (P + (a - i))) := by
    have e : vt x (Om1 * α + (P + (a - i))) = glA α (P + (a - i)) x := rfl
    rw [e, hv']
    exact hta.trans_le ((isNormal_veblen _).monotone (Ordinal.le_add_sub a i))
  unfold luZeta
  rw [if_pos ⟨P + (a - i), (add_lt_add_iff_left _).2 hc'', hcond⟩, gz_lg_add _ hd0]

omit hx hx1 in
/-- **`luL(a, q) = a·(1+q)` for `1 ≤ q < ω^ω`.** -/
theorem hc_luL_lt {q : Ordinal.{0}} (hq : q < ω ^ ω) (a : Ordinal.{0}) : luL a q = a * (1 + q) := by
  rcases lt_or_ge q ω with hqω | hqω
  · exact lu_luL_fin hqω
  rw [lu_luL_inf hqω, one_add_of_omega0_le hqω]
  have hq0 : q ≠ 0 := (lt_of_lt_of_le omega0_pos hqω).ne'
  have hb : log ω q < ω := (lt_opow_iff_log_lt one_lt_omega0 hq0).1 hq
  obtain ⟨n, hn⟩ := lt_omega0.1 hb
  have hb1 : log ω q ≠ 0 := (log_pos one_lt_omega0 hq0 hqω).ne'
  have hn0 : n ≠ 0 := by rintro rfl; exact hb1 (by rw [hn]; rfl)
  rw [hn, lg_nat hn0, add_zero, ← mul_add, Ordinal.add_sub_cancel_of_le]
  rw [← hn]; exact opow_log_le_self ω hq0

/-- **THE `R₁⁺`-REACH AT EVERY LEVEL `1 ≤ q < ω^ω`**: `lh(ϑˣ(Ω₁·q + t)) = ϑˣ(Ω₁·q + t)·(1+q) + ζ`,
`ζ = luZeta x q t < ϑˣ(Ω₁·q + t)`. -/
theorem hc_lhG {q t : Ordinal.{0}} (hq1 : 1 ≤ q) (hq : q < ω ^ ω) (ht : t ∈ Tset x) (ht1 : t < Om1) :
    IsLh1 (glA q t x) (glA q t x * (1 + q) + luZeta x q t) ∧ luZeta x q t < glA q t x := by
  have hqx : q < gq 1 x := hq.trans (hc_ww_lt_E (gm1_facts hx hx1).2.2.2)
  obtain ⟨hqT, hqΩ⟩ := gm1_T hx hx1 hqx
  obtain ⟨hL, hζ, -, -⟩ := gq_lh_th hx hx1 hq1 hqT hqΩ ht ht1
  rw [hc_luL_lt hq] at hL
  exact ⟨hL, hζ⟩

/-- `N_α(Γ_{x+1}) < Γ_{x+2}` for `α + 1 < Γ_{x+2}`. -/
theorem hcN_G_lt {α : Ordinal.{0}} (hαq : α + 1 < gq 1 x) : hcN α (lgG x) < gq 1 x := by
  obtain ⟨hkT, hk1⟩ := gm1_T hx hx1 hαq
  obtain ⟨hGT, -, hG1, -, -⟩ := lgG_facts hx hx1
  have h1 : (1 : Ordinal.{0}) ≤ α + 1 := le_add_self
  obtain ⟨b, hb⟩ := glA_P hx hx1 h1 hkT hk1 hGT hG1
  have hfix : veblen α (glA (α + 1) (lgG x) x) = glA (α + 1) (lgG x) x := by
    rw [← hb]; exact veblen_veblen_of_lt (lt_add_one α) b
  obtain ⟨-, -, -, -, -, hGa⟩ := glA_facts hx hx1 h1 hkT hk1 hGT hG1
  exact (hcN_le hfix hGa).trans_lt (lgVt_lt_low hx hx1 hkT hk1 hGT hG1 (gm1_one_T hx hx1).1
    (gm1_one_T hx hx1).2 hαq (mg_lgG_lt_G1 hx hx1))

end BaseG

end Googology.Trans.PoR.InaccPsi.R2.Hc
