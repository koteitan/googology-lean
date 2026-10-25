import Googology.Trans.PoR.InaccPsi.R2.HaImg

/-!
# HaImgP: LEMMA IMG OVER ANY `φ(2,·)`-FIXED PSEUDO-BASE, AND AT THE FIRST `ω` POINTS OF VEBLEN LEVEL 3

`Gz.gz_glA2V`, `Gz.gzI_limZ` and `Gz.gzImg_B3` work over the pseudo-base `Γ_{ρ+1}`.  Here the same over ANY fixed
point `P` of `φ(2, ·)` with `ρ < P < Γ_{ρ+2}`:

* `ha_low2` (**`ϑˣ(Ω₁·2 + σ) < P` for `σ < P`**), `ha_glA2_P` (**`ϑˣ(Ω₁·2 + P) = evZ(P)`**), `ha_glA2V_P`
  (**`ϑˣ(Ω₁·2 + P + ν) = φ(2, i₀ + ν)`**, `φ(2, i₀) = evZ(P)`, as long as no `φ(2,·)`-fixed point is passed);
* `haN` (**`N(P)`**, the least fixed point of `φ(2, ·)` above `evZ(P)`), `ha_nofix_N`, `haI_limZ_P` (**LEMMA IMG AT A
  LIMIT `ε`-FIXED POINT `φ(2, i₀ + c)` OVER `P`**), `ha_down_P` (**the reach test below `N(P)`**: Veblen level `1`
  or `2`), `ha_img_next` (**LEMMA IMG BELOW `N(P)`** given it up to `P`);
* `ha_glA3_succ` (**`ϑˣ(Ω₁·3 + t + 1) = N(ϑˣ(Ω₁·3 + t))`**), `haW3` (`W₃(x, n) = ϑˣ(Ω₁·3 + Γ_{x+1} + n) =
  φ(3, Γ_{x+1} + 1 + n)`), `ha_img_W3` (**LEMMA IMG FOR EVERY VALUE UP TO `φ(3, Γ_{ρ+1} + 1 + n)`, EVERY `n`**: the
  level-3 points by `Ha.ha_img_down` at `n = 3`, the points between by `ha_img_next`), `ha_pkg_W3`.

No new axiom.  New definitions: `haN`, `haW3`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ha

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Fixed points of `φ(2, ·)` -/

/-- **`N(P)`**, the least fixed point of `φ(2, ·)` above `evZ(P)`. -/
noncomputable def haN (P : Ordinal.{0}) : Ordinal.{0} := nfp (veblen 2) (evZ P + 1)

theorem haN_fix (P : Ordinal.{0}) : veblen 2 (haN P) = haN P := nfp_fp (isNormal_veblen 2) _

theorem haN_gt (P : Ordinal.{0}) : evZ P < haN P := (lt_add_one _).trans_le (le_nfp _ _)

theorem ha_inE_of_fix2 {P : Ordinal.{0}} (hP : veblen 2 P = P) : InE P := by
  have h : ω ^ veblen 2 P = veblen 2 P := gg_veblen_eps two_ne_zero
  rwa [hP] at h

theorem ha_fix1_of_fix2 {P : Ordinal.{0}} (hP : veblen 2 P = P) : veblen 1 P = P := by
  have h := veblen_veblen_of_lt (one_lt_two (α := Ordinal.{0})) P
  rwa [hP] at h

theorem ha_LuP3_of_fix2 {P : Ordinal.{0}} (hP : veblen 2 P = P) : LuP 3 P := by
  unfold LuP
  rw [mem_range_veblen three_ne_zero]
  intro b hb
  rcases lt_or_ge b 2 with hb2 | hb2
  · have h := veblen_veblen_of_lt hb2 P
    rwa [hP] at h
  · have : b = 2 := le_antisymm (Order.lt_add_one_iff.1 (by rw [ha_two_add_one]; exact hb)) hb2
    rw [this]; exact hP

theorem haN_E (P : Ordinal.{0}) : InE (haN P) := ha_inE_of_fix2 (haN_fix P)

/-- Every fixed point of `φ(2, ·)` above `evZ(P)` is at least `N(P)`. -/
theorem ha_fix_ge_N {P j : Ordinal.{0}} (hj : veblen 2 j = j) (hZj : evZ P < j) : haN P ≤ j :=
  nfp_le_fp (isNormal_veblen 2).strictMono.monotone (Order.add_one_le_of_lt hZj) hj.le

/-- `evZ(P) = φ(2, P + 1)` is not a fixed point of `φ(2, ·)`. -/
theorem ha_evZ_notfix {P : Ordinal.{0}} (hP : veblen 2 P = P) : veblen 2 (evZ P) ≠ evZ P := by
  intro e
  have h1 : evZ P = veblen 2 (P + 1) := by
    have := gz_evZ_veb2 P; rwa [hP] at this
  have hP1 : P + 1 < evZ P := (ev_isSuccLimit_of_inE (evZ_E P)).add_one_lt (lt_evZ P)
  have h2 := (isNormal_veblen 2).strictMono hP1
  rw [← h1, e] at h2
  exact lt_irrefl _ h2

theorem haB3_eq_N (x : Ordinal.{0}) : gzB3 x = haN (lgG x) := rfl

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`ϑˣ(Ω₁·2 + σ) < P` for every `σ < P`**, `P ∈ (x, Γ_{x+2})` a fixed point of `φ(2, ·)`. -/
theorem ha_low2 {P : Ordinal.{0}} (hP : veblen 2 P = P) (hxP : x < P) (hPq : P < gq 1 x) :
    ∀ σ, σ < P → glA 2 σ x < P := by
  obtain ⟨h2T, h21⟩ := gw_two_T hx hx1
  have hPE : InE P := ha_inE_of_fix2 hP
  have hP3 : LuP (2 + 1) P := by rw [ha_two_add_one]; exact ha_LuP3_of_fix2 hP
  have hP2 : LuP 2 P := ⟨P, hP⟩
  have h2P : (2 : Ordinal.{0}) < P := gw_two_lt_w.trans (omega0_lt_inE hPE)
  intro σ
  induction σ using WellFoundedLT.induction with
  | ind σ IH =>
  intro hσ
  obtain ⟨hσT, hσ1⟩ := gm1_T hx hx1 (hσ.trans hPq)
  have hle : glA 2 σ x ≤ P := glA_min hx hx1 one_le_two h2T h21 hσT hσ1 hP2 hxP hσ h2P
    (fun σ' h' => IH σ' h' (h'.trans hσ))
  exact lt_of_le_of_ne hle (fun e => glA_notP hx hx1 one_le_two h2T h21 hσT hσ1 (by rw [e]; exact hP3))

/-- **`ϑˣ(Ω₁·2 + P) = evZ(P)`** at every fixed point `P ∈ (x, Γ_{x+2})` of `φ(2, ·)`. -/
theorem ha_glA2_P {P : Ordinal.{0}} (hP : veblen 2 P = P) (hxP : x < P) (hPq : P < gq 1 x) :
    glA 2 P x = evZ P := by
  obtain ⟨h2T, h21⟩ := gw_two_T hx hx1
  obtain ⟨hPT, hP1⟩ := gm1_T hx hx1 hPq
  have hPE : InE P := ha_inE_of_fix2 hP
  have h2P : (2 : Ordinal.{0}) < P := gw_two_lt_w.trans (omega0_lt_inE hPE)
  refine le_antisymm ?_ ?_
  · exact glA_min hx hx1 one_le_two h2T h21 hPT hP1 (gw_LuP2 P) (hxP.trans (lt_evZ _)) (lt_evZ _)
      (h2P.trans (lt_evZ _)) (fun σ hσ => (ha_low2 hx hx1 hP hxP hPq σ hσ).trans (lt_evZ _))
  · obtain ⟨-, -, -, -, -, hta⟩ := glA_facts hx hx1 one_le_two h2T h21 hPT hP1
    obtain ⟨k, hk⟩ := glA_P hx hx1 one_le_two h2T h21 hPT hP1
    have hfix : Ordinal.epsilon (glA 2 P x) = glA 2 P x := by
      rw [← hk]; exact veblen_veblen_of_lt one_lt_two k
    exact evZ_le hta hfix

/-- **`ϑˣ(Ω₁·2 + P + ν) = φ(2, i₀ + ν)`** (`ϑˣ(Ω₁·2 + P) = φ(2, i₀)`) for every `ν` with `P + ν < Γ_{x+2}` and no
`φ(2,·)`-fixed point `i₀ + ν'`, `ν' ≤ ν` a limit. -/
theorem ha_glA2V_P {P i0 : Ordinal.{0}} (hPq : P < gq 1 x) (hG0 : glA 2 P x = veblen 2 i0) : ∀ ν, P + ν < gq 1 x →
    (∀ ν', ν' ≤ ν → IsSuccLimit ν' → i0 + ν' < veblen 2 (i0 + ν')) →
    glA 2 (P + ν) x = veblen 2 (i0 + ν) := by
  obtain ⟨h2T, h21⟩ := gw_two_T hx hx1
  have h12 : (1 : Ordinal.{0}) ≤ 2 := one_le_two
  obtain ⟨hGT, hG1⟩ := gm1_T hx hx1 hPq
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hq hfix
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 hq
  rcases Ordinal.zero_or_succ_or_isSuccLimit ν with h0 | ⟨d, hd⟩ | hlim
  · subst h0; rw [add_zero, add_zero]; exact hG0
  · have hd' : ν = d + 1 := by rw [← succ_eq_add_one]; first | exact hd | exact hd.symm
    subst hd'
    have hdq : P + d < gq 1 x := lt_of_le_of_lt (add_le_add le_rfl le_self_add) hq
    have IHd := IH d (lt_add_one d) hdq (fun ν' h hl => hfix ν' (h.trans le_self_add) hl)
    rw [← add_assoc] at hq ⊢
    rw [gz_glA2_succ hx hx1 hq, IHd, ← add_assoc, gz_evZ_veb2]
  · have hval : ∀ ν'', ν'' < ν → glA 2 (P + ν'') x = veblen 2 (i0 + ν'') := fun ν'' h =>
      IH ν'' h ((add_lt_add_iff_left _).2 h |>.trans hq) (fun ν' h' hl => hfix ν' (h'.trans h.le) hl)
    set u := veblen 2 (i0 + ν) with hu
    have huE : InE u := gg_veblen_eps two_ne_zero
    have hiu : veblen 2 i0 < u := (isNormal_veblen 2).strictMono (lt_add_of_pos_right _ hlim.bot_lt)
    obtain ⟨-, hxa, -, -, h2a, hGa⟩ := glA_facts hx hx1 h12 h2T h21 hGT hG1
    rw [hG0] at hxa h2a hGa
    have htu : P + ν < u := (inE_indec huE).add_lt (hGa.trans hiu)
      ((le_add_self : ν ≤ i0 + ν).trans_lt (hfix ν le_rfl hlim))
    refine le_antisymm ?_ ?_
    · refine glA_min hx hx1 h12 h2T h21 htT ht1 ⟨_, rfl⟩ (hxa.trans hiu) htu (h2a.trans hiu) (fun σ hσ => ?_)
      rcases lt_or_ge σ P with hσP | hσP
      · obtain ⟨hσT, hσ1⟩ := gm1_T hx hx1 (hσP.trans hPq)
        have := glA_lt_of hx hx1 h12 h2T h21 hσT hGT hG1 hσP
        rw [hG0] at this
        exact this.trans hiu
      · obtain ⟨ν'', rfl⟩ := exists_add_of_le hσP
        have hν'' : ν'' < ν := (add_lt_add_iff_left _).1 hσ
        rw [hval ν'' hν'']
        exact (isNormal_veblen 2).strictMono ((add_lt_add_iff_left _).2 hν'')
    · refine ((isNormal_veblen 2).le_iff_forall_le (isSuccLimit_add _ hlim)).2 fun c hc => ?_
      rcases lt_or_ge c i0 with hci | hci
      · refine ((isNormal_veblen 2).strictMono hci).le.trans ?_
        rw [← hG0]
        exact (glA_le_iff hx hx1 h12 h2T h21 hGT hG1 htT ht1).2 le_self_add
      · obtain ⟨c', rfl⟩ := exists_add_of_le hci
        have hc' : c' < ν := (add_lt_add_iff_left _).1 hc
        have hq' : P + c' < gq 1 x := ((add_lt_add_iff_left _).2 hc').trans hq
        obtain ⟨hcT, -⟩ := gm1_T hx hx1 hq'
        rw [← hval c' hc']
        exact (glA_lt_of hx hx1 h12 h2T h21 hcT htT ht1 ((add_lt_add_iff_left _).2 hc')).le

/-- Below `N(P)` no index `j ≥ i₀` (`φ(2, i₀) = evZ(P)`) is a fixed point of `φ(2, ·)`. -/
theorem ha_nofix_N {P i0 j : Ordinal.{0}} (hP : veblen 2 P = P) (hi0 : veblen 2 i0 = evZ P) (hij : i0 ≤ j)
    (hjB : veblen 2 j < haN P) : j < veblen 2 j := by
  rcases (right_le_veblen 2 j).lt_or_eq with h | h
  · exact h
  · exfalso
    have hZj : evZ P ≤ j := by
      rw [← hi0, h]; exact (isNormal_veblen 2).monotone hij
    have hne : evZ P ≠ j := fun e => ha_evZ_notfix hP (by rw [e]; exact h.symm)
    have := ha_fix_ge_N h.symm (lt_of_le_of_ne hZj hne)
    exact absurd hjB (not_lt.2 (this.trans h.le))

/-- **`ϑˣ(Ω₁·3 + t + 1) = N(ϑˣ(Ω₁·3 + t))`**: the next point of Veblen level `3`. -/
theorem ha_glA3_succ {t : Ordinal.{0}} (ht : t + 1 < gq 1 x) : glA 3 (t + 1) x = haN (glA 3 t x) := by
  have ht' : t < gq 1 x := (lt_add_one t).trans ht
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 ht'
  obtain ⟨hsT, hs1⟩ := gm1_T hx hx1 ht
  have hq := (gm1_facts hx hx1).2.2.2
  have h3q : (3 : Ordinal.{0}) < gq 1 x := (natCast_lt_omega0 3).trans (omega0_lt_inE hq)
  obtain ⟨h3T, h31⟩ := gm1_T hx hx1 h3q
  have h13 : (1 : Ordinal.{0}) ≤ 3 := by norm_num
  obtain ⟨-, hxa, -, -, h3a, hta⟩ := glA_facts hx hx1 h13 h3T h31 htT ht1
  have hNlim : IsSuccLimit (haN (glA 3 t x)) := ev_isSuccLimit_of_inE (haN_E _)
  have hPN : glA 3 t x < haN (glA 3 t x) := (lt_evZ _).trans (haN_gt _)
  refine le_antisymm ?_ ?_
  · refine glA_min hx hx1 h13 h3T h31 hsT hs1 (ha_LuP3_of_fix2 (haN_fix _)) (hxa.trans hPN)
      (hNlim.add_one_lt (hta.trans hPN)) (h3a.trans hPN) (fun σ hσ => ?_)
    have hσt : σ ≤ t := Order.lt_add_one_iff.1 hσ
    obtain ⟨hσT, hσ1⟩ := gm1_T hx hx1 (lt_of_le_of_lt hσt ht')
    exact lt_of_le_of_lt ((glA_le_iff hx hx1 h13 h3T h31 hσT hσ1 htT ht1).2 hσt) hPN
  · obtain ⟨k, hk⟩ := glA_P hx hx1 h13 h3T h31 hsT hs1
    obtain ⟨k0, hk0⟩ := glA_P hx hx1 h13 h3T h31 htT ht1
    have hfix2 : veblen 2 (glA 3 (t + 1) x) = glA 3 (t + 1) x := by
      rw [← hk]; exact veblen_veblen_of_lt (by norm_num) k
    have hfix1 : Ordinal.epsilon (glA 3 (t + 1) x) = glA 3 (t + 1) x := by
      rw [← hk]; exact veblen_veblen_of_lt (by norm_num) k
    have hP2 : veblen 2 (glA 3 t x) = glA 3 t x := by rw [← hk0]; exact veblen_veblen_of_lt (by norm_num) k0
    have hlt : glA 3 t x < glA 3 (t + 1) x := glA_lt_of hx hx1 h13 h3T h31 htT hsT hs1 (lt_add_one t)
    have hZ : evZ (glA 3 t x) ≤ glA 3 (t + 1) x := evZ_le hlt hfix1
    have hne : evZ (glA 3 t x) ≠ glA 3 (t + 1) x := fun e => ha_evZ_notfix hP2 (by rw [e]; exact hfix2)
    exact ha_fix_ge_N hfix2 (lt_of_le_of_ne hZ hne)

end Base

/-! ## Lemma IMG over a pseudo-base `P` -/

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG AT A LIMIT `ε`-FIXED POINT `E = φ(2, i₀ + c)` OVER A `φ(2,·)`-FIXED PSEUDO-BASE `P`**
(`φ(2, i₀) = evZ(P)`, `c` a limit, `P + c < Γ_{ρ+2}`, no `φ(2,·)`-fixed point `i₀ + ν'`, `ν' ≤ c`), given Lemma IMG for
every value below `E`. -/
theorem haI_limZ_P {P i0 c : Ordinal.{0}} (hP : veblen 2 P = P) (hρP : ρ < P) (hPq : P < gq 1 ρ)
    (hi0 : veblen 2 i0 = evZ P) (hlim : IsSuccLimit c)
    (hq : P + c < gq 1 ρ) (hfix : ∀ ν', ν' ≤ c → IsSuccLimit ν' → i0 + ν' < veblen 2 (i0 + ν'))
    (IH : ∀ u, u < veblen 2 (i0 + c) → GnI ρ δ u) : GnI ρ δ (veblen 2 (i0 + c)) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hG0 : glA 2 P ρ = veblen 2 i0 := by rw [hi0]; exact ha_glA2_P hρE hρ1 hP hρP hPq
  have hc0 : c ≠ 0 := hlim.bot_lt.ne'
  have hEv : glA 2 (P + c) ρ = veblen 2 (i0 + c) := ha_glA2V_P hρE hρ1 hPq hG0 c hq hfix
  set E := veblen 2 (i0 + c) with hEdef
  obtain ⟨h2T, h21⟩ := gw_two_T hρE hρ1
  obtain ⟨htT, ht1⟩ := gm1_T hρE hρ1 hq
  obtain ⟨hET0, hρE', hE1, hE, -, htE⟩ := glA_facts hρE hρ1 one_le_two h2T h21 htT ht1
  rw [hEv] at hET0 hρE' hE1 hE htE
  have hET : E ∈ Tset ρ ∧ E < Om1 := ⟨hET0, hE1⟩
  have hEδ : E < δ := gn_lt_δ h hET.1 hET.2
  have hδI := inE_indec h.δE
  have hEEδ : E + E < δ := hδI.add_lt hEδ hEδ
  have hEEEδ : E + E + E < δ := hδI.add_lt hEEδ hEδ
  obtain ⟨c', hcs, hdvd, hc'c⟩ := lg_split hc0
  set z := lg c with hzdef
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz, opow_zero] at hcs
    exact not_isSuccLimit_succ c' (by rw [succ_eq_add_one, ← hcs]; exact hlim)
  set E' := veblen 2 (i0 + c') with hE'def
  have hE'E : E' < E := (isNormal_veblen 2).strictMono ((add_lt_add_iff_left _).2 hc'c)
  have hcE : c < E := (le_add_self : c ≤ i0 + c).trans_lt (hfix c le_rfl hlim)
  have hzE : z < E := (lg_le hc0).trans_lt hcE
  have hlhE : IsLh1 E (E + E + E + z) := by
    have hL := gl_lh_th (k := 2) hρE hρ1 (by norm_num) htT ht1
    have hz' : glZeta ρ 2 (P + c) = z := by
      rw [gz_glZeta_eq (lt_of_lt_of_le hlim.bot_lt (le_add_self : c ≤ P + c)).ne' ?_, gz_lg_add _ hc0]
      obtain ⟨a, ha, hta⟩ := ((isNormal_veblen 2).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 htE
      have hc'' : a - i0 < c := by
        rcases lt_or_ge a i0 with hai | hai
        · rw [Ordinal.sub_eq_zero_iff_le.2 hai.le]; exact hlim.bot_lt
        · have : i0 + (a - i0) < i0 + c := by rw [Ordinal.add_sub_cancel_of_le hai]; exact ha
          exact (add_lt_add_iff_left _).1 this
      refine ⟨P + (a - i0), (add_lt_add_iff_left _).2 hc'', ?_⟩
      have hq'' : P + (a - i0) < gq 1 ρ := ((add_lt_add_iff_left _).2 hc'').trans hq
      rw [gz_vt2, ha_glA2V_P hρE hρ1 hPq hG0 _ hq'' (fun ν' h' hl => hfix ν' (h'.trans hc''.le) hl)]
      exact hta.trans_le ((isNormal_veblen 2).monotone (Ordinal.le_add_sub a i0))
    rw [gz_vt2, hEv, hz', gz_mul3] at hL
    exact hL
  have hEEEz : E + E + E < E + E + E + z := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0)
  have hEEEzδ : E + E + E + z < δ := hδI.add_lt hEEEδ (hzE.trans hEδ)
  have hsrc : le1 E (E + E + E + z) := (h.lowδ _ _ hρE' hEEEzδ.le).2 hlhE.1
  obtain ⟨W1, Z1, w1, m1, -, -, b1⟩ := gnI_use h (IH E' hE'E)
  obtain ⟨W2, Z2, w2, m2, -, -, b2⟩ := gnI_use h (IH z hzE)
  have hEE : E < E + E := lt_add_of_pos_right _ hE.pos
  have hEEE : E + E < E + E + E := lt_add_of_pos_right _ hE.pos
  have w3 := (w1.union w2).insW hρE'.le hEδ (Or.inl (inE_indec hE))
  have w4 := w3.insW (hρE'.le.trans le_self_add) hEEδ (Or.inr ⟨E, by simp, E, by simp, hEE, hEE, rfl⟩)
  have w5 := w4.insW ((hρE'.le.trans le_self_add).trans le_self_add) hEEEδ
    (Or.inr ⟨E + E, by simp, E, by simp, hEEE, hEE.trans hEEE, rfl⟩)
  have w6 := w5.insW (((hρE'.le.trans le_self_add).trans le_self_add).trans le_self_add) hEEEzδ
    (Or.inr ⟨E + E + E, by simp, z, by rcases Finset.mem_union.1 m2 with hm | hm <;> simp [hm], hEEEz,
      hzE.trans ((hEE.trans hEEE).trans hEEEz), rfl⟩)
  refine gnI_mk h w6 (by simp) hET.1 hET.2 (fun A f hW hZ C => ?_)
  have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  obtain ⟨hE'A, hE'TB, pE'⟩ := b1 A f hW1 hZ1 C
  obtain ⟨hzA, hzTB, pz⟩ := b2 A f hW2 hZ2 C
  have hEA : E ∈ A := hW (by simp)
  have hEEA : E + E ∈ A := hW (by simp)
  have hEEEA : E + E + E ∈ A := hW (by simp)
  have hEEEzA : E + E + E + z ∈ A := hW (by simp)
  have hETB : E ∈ TB ρ (f ρ) := gnI_TB h C hET.1 (fun p hp => hZ (by simp [hp]))
  have hB := h.img_bases C
  by_contra hlt
  push Not at hlt
  by_cases hU : UpsPt (f E)
  · exact absurd (gw_pbig h hET hρE' A f C hEA hETB hU) (not_lt.2 hlt.le)
  have himg : le1 (f E) (f E + f E + f E + f z) := by
    have := C.cov1 _ hEA _ hEEEzA hsrc
    rwa [← C.add _ hEEEA _ hzA _ hEEEzA rfl, ← C.add _ hEEA _ hEA _ hEEEA rfl,
      ← C.add _ hEA _ hEA _ hEEA rfl] at this
  have hR := (C.sk _ (C.low _ hEA) hU _).1 himg
  obtain ⟨u, huTB, hpu, hE'u, huE, huI⟩ :=
    gw_key h hE hET hρE' hEEδ A f C hEA hEEA hETB E' hE'E hE'A hE'TB pE' hlt
  have hu1 : u < Om1 := huE.trans hET.2
  have hZE' : evZ P ≤ E' := by rw [← hi0]; exact (isNormal_veblen 2).monotone le_self_add
  have hρu : ρ < u := ((hρP.trans (lt_evZ _)).trans_le hZE').trans hE'u
  obtain ⟨l, hl, hlTB, hpl⟩ := lh_pi hB huTB hρu hu1
  obtain ⟨huu1, huu2⟩ := pi_add hB huTB huTB
  have hle0 := hpl.2 _ (by rw [hpu]; exact hR)
  obtain ⟨j, hj1, hj2⟩ := gz_floor (j0 := i0 + c') hE'u.le
  rcases hj1.lt_or_eq with hju | hju
  · have hZE : InE (veblen 2 j) := gg_veblen_eps two_ne_zero
    have hZ1 : veblen 2 j < Om1 := hju.trans hu1
    obtain ⟨d, hd⟩ := evA_surj hZE huI hju.le
    have hd0 : d ≠ 0 := by rintro rfl; rw [evA_zero hZE] at hd; exact hju.ne hd
    have hdZ : d < evZ (veblen 2 j) := by
      by_contra hge; push Not at hge
      have : evZ (veblen 2 j) ≤ u := hge.trans ((le_evA_idx _ d).trans hd.le)
      rw [gz_evZ_veb2] at this
      exact absurd hj2 (not_lt.2 this)
    have hlhu : IsLh1 u (u * 2 + lg d) := by rw [← hd]; exact gk_lh_evA hZE hZ1 hd0 hdZ
    have hl' : l = u + u + lg d := by rw [lkcIsLh1_unique hl hlhu, mul_two_eq]
    rw [hl'] at hlTB hle0
    have hld : lg d < u := (lg_le hd0).trans_lt (by rw [← hd]; exact lt_evA_self hZE hdZ)
    have hlg1 : u + u + lg d < Om1 :=
      (inE_indec gl_Om1_E).add_lt ((inE_indec gl_Om1_E).add_lt hu1 hu1) (hld.trans hu1)
    obtain ⟨hdTB, -⟩ := TB_sub hB huu1 hlTB le_self_add hlg1
    rw [Ordinal.add_sub_cancel] at hdTB
    obtain ⟨-, hps⟩ := pi_add hB huu1 hdTB
    rw [hps, huu2, hpu, add_assoc (f E + f E) (f E) (f z)] at hle0
    have hfz : f E + f z ≤ pi (f ρ) ρ (lg d) := (add_le_add_iff_left _).1 hle0
    have hud : u ≤ lg d :=
      ((pi_bijOn hB).2.le_iff_le huTB hdTB).1 (by rw [hpu]; exact le_self_add.trans hfz)
    exact absurd hud (not_le.2 hld)
  · have hj' : i0 + c' < j := by
      have : veblen 2 (i0 + c') < veblen 2 j := by rw [hju]; exact hE'u
      exact (isNormal_veblen 2).strictMono.lt_iff_lt.1 this
    have hjE : j < i0 + c := by
      have : veblen 2 j < veblen 2 (i0 + c) := by rw [hju]; exact huE
      exact (isNormal_veblen 2).strictMono.lt_iff_lt.1 this
    have hi0j : i0 ≤ j := le_self_add.trans hj'.le
    obtain ⟨d, rfl⟩ := exists_add_of_le hi0j
    have hc'd : c' < d := (add_lt_add_iff_left _).1 hj'
    have hdc : d < c := (add_lt_add_iff_left _).1 hjE
    have hd0 : d ≠ 0 := (lt_of_le_of_lt zero_le hc'd).ne'
    have hqd : P + d < gq 1 ρ := ((add_lt_add_iff_left _).2 hdc).trans hq
    obtain ⟨hdT, hd1⟩ := gm1_T hρE hρ1 hqd
    have hL := gl_lh_th (k := 2) hρE hρ1 (by norm_num) hdT hd1
    rw [gz_vt2, ha_glA2V_P hρE hρ1 hPq hG0 d hqd (fun ν' h' hl => hfix ν' (h'.trans hdc.le) hl), hju,
      gz_mul3] at hL
    have hζlg : glZeta ρ 2 (P + d) ≤ lg d := (gz_glZeta_le ρ (P + d) 2).trans (gz_lg_add _ hd0).le
    have hl' : l = u + u + u + glZeta ρ 2 (P + d) := lkcIsLh1_unique hl hL
    rw [hl'] at hlTB hle0
    have huuu1 : u + u + u < Om1 :=
      (inE_indec gl_Om1_E).add_lt ((inE_indec gl_Om1_E).add_lt hu1 hu1) hu1
    have hζ1 : glZeta ρ 2 (P + d) < Om1 := hζlg.trans_lt ((lg_le hd0).trans_lt (hdc.trans (hcE.trans hET.2)))
    have hlg1 : u + u + u + glZeta ρ 2 (P + d) < Om1 := (inE_indec gl_Om1_E).add_lt huuu1 hζ1
    obtain ⟨huuu, huuu2⟩ := pi_add hB huu1 huTB
    obtain ⟨hζTB, -⟩ := TB_sub hB huuu hlTB le_self_add hlg1
    rw [Ordinal.add_sub_cancel] at hζTB
    obtain ⟨-, hps⟩ := pi_add hB huuu hζTB
    rw [hps, huuu2, huu2, hpu] at hle0
    have hfz : f z ≤ pi (f ρ) ρ (glZeta ρ 2 (P + d)) := (add_le_add_iff_left _).1 hle0
    have hzζ : z ≤ glZeta ρ 2 (P + d) := ((pi_bijOn hB).2.le_iff_le hzTB hζTB).1 (pz.trans hfz)
    have hdiv : ω ^ z ∣ d := (le_lg_iff hd0 z).1 (hzζ.trans hζlg)
    obtain ⟨δ', hδ'⟩ : ∃ δ', d = c' + δ' := ⟨d - c', (Ordinal.add_sub_cancel_of_le hc'd.le).symm⟩
    have hδ0 : δ' ≠ 0 := by rintro rfl; rw [add_zero] at hδ'; exact absurd hδ' hc'd.ne'
    have hδlt : δ' < ω ^ z := by
      have : c' + δ' < c' + ω ^ z := by rw [← hδ', ← hcs]; exact hdc
      exact (add_lt_add_iff_left _).1 this
    have hdivδ : ω ^ z ∣ δ' := (dvd_add_iff hdvd).1 (by rw [← hδ']; exact hdiv)
    exact absurd (Ordinal.le_of_dvd hδ0 hdivδ) (not_le.2 hδlt)

/-- **The reach test below `N(P)`**: every `ε`-number `u ∈ (evZ(P), N(P))` has Veblen level `1` (reach `u·2 + lg d`)
or `2` (reach `u·3 + ζ`), `ζ < u`. -/
theorem ha_down_P {P u : Ordinal.{0}} (hP : veblen 2 P = P) (hρP : ρ < P) (hNq : haN P < gq 1 ρ) (hu : InE u)
    (hZu : evZ P < u) (huB : u < haN P) :
    ∃ m : ℕ, ∃ ζ, m ≤ 2 ∧ IsLh1 u (u * ((m : Ordinal.{0}) + 1) + ζ) ∧ ζ < u := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hPq : P < gq 1 ρ := ((lt_evZ P).trans (haN_gt P)).trans hNq
  have hu1 : u < Om1 := (huB.trans hNq).trans (gm1_facts hρE hρ1).2.2.1
  obtain ⟨i0, hi0⟩ := gw_LuP2 P
  have hG0 : glA 2 P ρ = veblen 2 i0 := by rw [hi0]; exact ha_glA2_P hρE hρ1 hP hρP hPq
  obtain ⟨j, hj1, hj2⟩ := gz_floor (u := u) (j0 := i0) (by rw [hi0]; exact hZu.le)
  have hi0j : i0 ≤ j := by
    have : veblen 2 i0 < veblen 2 (j + 1) := by rw [hi0]; exact hZu.trans hj2
    exact Order.lt_add_one_iff.1 ((isNormal_veblen 2).strictMono.lt_iff_lt.1 this)
  rcases hj1.lt_or_eq with hju | hju
  · have hZE : InE (veblen 2 j) := gg_veblen_eps two_ne_zero
    have hZ1 : veblen 2 j < Om1 := hju.trans hu1
    obtain ⟨d, hd⟩ := evA_surj hZE hu hju.le
    have hd0 : d ≠ 0 := by rintro rfl; rw [evA_zero hZE] at hd; exact hju.ne hd
    have hdZ : d < evZ (veblen 2 j) := by
      by_contra hge; push Not at hge
      have : evZ (veblen 2 j) ≤ u := hge.trans ((le_evA_idx _ d).trans hd.le)
      rw [gz_evZ_veb2] at this
      exact absurd hj2 (not_lt.2 this)
    have hlhu : IsLh1 u (u * 2 + lg d) := by rw [← hd]; exact gk_lh_evA hZE hZ1 hd0 hdZ
    have hld : lg d < u := (lg_le hd0).trans_lt (by rw [← hd]; exact lt_evA_self hZE hdZ)
    refine ⟨1, lg d, by norm_num, ?_, hld⟩
    rw [Nat.cast_one, one_add_one_eq_two]; exact hlhu
  · obtain ⟨d, rfl⟩ := exists_add_of_le hi0j
    have hnf : ∀ ν', ν' ≤ d → IsSuccLimit ν' → i0 + ν' < veblen 2 (i0 + ν') := fun ν' h' _ =>
      ha_nofix_N hρE hρ1 hP hi0 le_self_add
        (((isNormal_veblen 2).monotone ((add_le_add_iff_left _).2 h')).trans_lt (hju ▸ huB))
    have hdu : d < u := (le_add_self : d ≤ i0 + d).trans_lt (by
      rw [← hju]; exact ha_nofix_N hρE hρ1 hP hi0 le_self_add (hju ▸ huB))
    have hq : P + d < gq 1 ρ :=
      (inE_indec (gm1_facts hρE hρ1).2.2.2).add_lt hPq (hdu.trans (huB.trans hNq))
    obtain ⟨hdT, hd1⟩ := gm1_T hρE hρ1 hq
    have hval : glA 2 (P + d) ρ = u := by rw [← hju]; exact ha_glA2V_P hρE hρ1 hPq hG0 d hq hnf
    have hL := gl_lh_th (k := 2) hρE hρ1 (by norm_num) hdT hd1
    rw [gz_vt2, hval] at hL
    obtain ⟨h2T, h21⟩ := gw_two_T hρE hρ1
    obtain ⟨-, -, -, -, -, htu⟩ := glA_facts hρE hρ1 one_le_two h2T h21 hdT hd1
    rw [hval] at htu
    have hG0' : P + d ≠ 0 := ((hρE.pos.trans hρP).trans_le le_self_add).ne'
    have hζ : glZeta ρ 2 (P + d) < u := ((gz_glZeta_le ρ _ 2).trans (lg_le hG0')).trans_lt htu
    refine ⟨2, glZeta ρ 2 (P + d), le_rfl, ?_, hζ⟩
    push_cast at hL ⊢
    exact hL

/-- **LEMMA IMG BELOW `N(P)`** over a fixed point `P ∈ (ρ, Γ_{ρ+2})` of `φ(2, ·)`, given Lemma IMG up to `P`: the
`ε`-numbers in `(P, evZ(P))` (`Gw.gwI_epsP`), `evZ(P)` and every successor `ε`-fixed point (`Gw.gwI_fixZ`), the limit
`ε`-fixed points (`haI_limZ_P`). -/
theorem ha_img_next {P : Ordinal.{0}} (hP : veblen 2 P = P) (hρP : ρ < P) (hNq : haN P < gq 1 ρ)
    (hle : ∀ v, v ≤ P → GnI ρ δ v) : ∀ v, v < haN P → GnI ρ δ v := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hPq : P < gq 1 ρ := ((lt_evZ P).trans (haN_gt P)).trans hNq
  have hPI : InE P := ha_inE_of_fix2 hP
  obtain ⟨i0, hi0⟩ := gw_LuP2 P
  refine gnImg_of_eps h (fun v hv => gm1_T hρE hρ1 (hv.trans hNq)) (fun e he _ heB IHe => ?_)
  rcases le_or_gt e P with heP | hPe
  · exact hle e heP
  rcases lt_trichotomy e (evZ P) with hlt | heq | hgt
  · exact gwI_epsP h hPI hρP hPq he hPe hlt IHe
  · rw [heq] at IHe ⊢; exact gwI_fixZ h hPI hρP hPq IHe
  · obtain ⟨j, hj1, hj2⟩ := gz_floor (u := e) (j0 := i0) (by rw [hi0]; exact hgt.le)
    have hi0j : i0 ≤ j := by
      have : veblen 2 i0 < veblen 2 (j + 1) := by rw [hi0]; exact hgt.trans hj2
      exact Order.lt_add_one_iff.1 ((isNormal_veblen 2).strictMono.lt_iff_lt.1 this)
    have hZj : evZ P ≤ veblen 2 j := by rw [← hi0]; exact (isNormal_veblen 2).monotone hi0j
    have hρZ : ρ < evZ P := hρP.trans (lt_evZ _)
    rcases hj1.lt_or_eq with hjlt | hjeq
    · exact gwI_epsP h (gg_veblen_eps two_ne_zero) (hρZ.trans_le hZj) (hjlt.trans (heB.trans hNq)) he hjlt
        (by rw [gz_evZ_veb2]; exact hj2) IHe
    · obtain ⟨d, rfl⟩ := exists_add_of_le hi0j
      rcases zero_or_succ_or_isSuccLimit d with h0 | ⟨d', hd'⟩ | hlim
      · subst h0
        rw [add_zero, hi0] at hjeq
        exact absurd hjeq hgt.ne
      · have e1 : i0 + d = (i0 + d') + 1 := by rw [← hd', succ_eq_add_one, add_assoc]
        rw [e1, ← gz_evZ_veb2] at hjeq
        subst hjeq
        have hZd' : evZ P ≤ veblen 2 (i0 + d') := by
          rw [← hi0]; exact (isNormal_veblen 2).monotone le_self_add
        exact gwI_fixZ h (gg_veblen_eps two_ne_zero) (hρZ.trans_le hZd') ((lt_evZ _).trans (heB.trans hNq)) IHe
      · subst hjeq
        have hnf : ∀ ν', ν' ≤ d → i0 + ν' < veblen 2 (i0 + ν') := fun ν' h' =>
          ha_nofix_N hρE hρ1 hP hi0 le_self_add
            (((isNormal_veblen 2).monotone ((add_le_add_iff_left _).2 h')).trans_lt heB)
        have hq : P + d < gq 1 ρ :=
          (inE_indec (gm1_facts hρE hρ1).2.2.2).add_lt hPq
            (((le_add_self : d ≤ i0 + d).trans_lt (hnf d le_rfl)).trans (heB.trans hNq))
        exact haI_limZ_P h hP hρP hPq hi0 hlim hq (fun ν' h' _ => hnf ν' h') IHe

end Img

/-! ## The first `ω` points of Veblen level 3 -/

/-- **`W₃(x, n) = ϑˣ(Ω₁·3 + Γ_{x+1} + n) = φ(3, Γ_{x+1} + 1 + n)`.** -/
noncomputable def haW3 (x : Ordinal.{0}) (n : ℕ) : Ordinal.{0} := glA 3 (lgG x + n) x

section W3

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem haW3_q (n : ℕ) : lgG x + n < gq 1 x :=
  (inE_indec (gm1_facts hx hx1).2.2.2).add_lt (mg_lgG_lt_G1 hx hx1)
    ((natCast_lt_omega0 n).trans ((omega0_lt_inE hx).trans (gm1_facts hx hx1).2.1))

theorem haW3_zero : haW3 x 0 = gzB3 x := by
  unfold haW3; rw [Nat.cast_zero, add_zero]; exact ha_B3_eq hx hx1

theorem haW3_succ (n : ℕ) : haW3 x (n + 1) = haN (haW3 x n) := by
  unfold haW3
  rw [Nat.cast_succ, ← add_assoc]
  exact ha_glA3_succ hx hx1 (by rw [add_assoc, ← Nat.cast_succ]; exact haW3_q hx hx1 (n + 1))

theorem haW3_facts (n : ℕ) : veblen 2 (haW3 x n) = haW3 x n ∧ x < haW3 x n ∧ haW3 x n < gq 1 x := by
  have hq := (gm1_facts hx hx1).2.2.2
  have h3q : (3 : Ordinal.{0}) < gq 1 x := (natCast_lt_omega0 3).trans (omega0_lt_inE hq)
  obtain ⟨h3T, h31⟩ := gm1_T hx hx1 h3q
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 (haW3_q hx hx1 n)
  have h13 : (1 : Ordinal.{0}) ≤ 3 := by norm_num
  obtain ⟨k, hk⟩ := glA_P hx hx1 h13 h3T h31 htT ht1
  obtain ⟨-, hxa, -, -, -, -⟩ := glA_facts hx hx1 h13 h3T h31 htT ht1
  refine ⟨?_, hxa, lgVt_lt_low hx hx1 h3T h31 htT ht1 (gm1_one_T hx hx1).1 (gm1_one_T hx hx1).2 h3q
    (haW3_q hx hx1 n)⟩
  show veblen 2 (glA 3 _ x) = glA 3 _ x
  rw [← hk]; exact veblen_veblen_of_lt (by norm_num) k

end W3

section ImgW3

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG AT THE NEXT POINT OF VEBLEN LEVEL 3**: `N(W₃(ρ, n)) = W₃(ρ, n+1)`, by the reach test going down at
level `3` (`Ha.ha_img_down`; the `ε`-numbers in `(evZ(W₃(ρ, n)), W₃(ρ, n+1))` have level `1` or `2`). -/
theorem ha_img_W3succ (n : ℕ) (hle : ∀ v, v < haW3 ρ (n + 1) → GnI ρ δ v) : GnI ρ δ (haW3 ρ (n + 1)) := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨hPf, hρP, -⟩ := haW3_facts hρE hρ1 n
  obtain ⟨-, -, hNq'⟩ := haW3_facts hρE hρ1 (n + 1)
  have hN : haW3 ρ (n + 1) = haN (haW3 ρ n) := haW3_succ hρE hρ1 n
  have hNq : haN (haW3 ρ n) < gq 1 ρ := hN ▸ hNq'
  obtain ⟨htT, ht1⟩ := gm1_T hρE hρ1 (haW3_q hρE hρ1 (n + 1))
  have e3 : glA ((3 : ℕ) : Ordinal.{0}) (lgG ρ + ((n + 1 : ℕ) : Ordinal.{0})) ρ = haW3 ρ (n + 1) := by
    rw [Nat.cast_ofNat]; rfl
  have hZN : evZ (haW3 ρ n) < glA ((3 : ℕ) : Ordinal.{0}) (lgG ρ + ((n + 1 : ℕ) : Ordinal.{0})) ρ := by
    rw [e3, hN]; exact haN_gt _
  have H := ha_img_down h (n := 3) (by norm_num) htT ht1 (hρP.trans (lt_evZ _)) hZN
    (fun u hu hZu huB => by
      rw [e3, hN] at huB
      obtain ⟨m, ζ, hm, hl, hζ⟩ := ha_down_P h hPf hρP hNq hu hZu huB
      exact ⟨m, ζ, hm.trans (by norm_num), hl, hζ, fun e => absurd e (by omega)⟩)
    (fun u hu => hle u (by rw [e3] at hu; exact hu))
  rwa [e3] at H

/-- **LEMMA IMG FOR EVERY VALUE UP TO `φ(3, Γ_{ρ+1} + 1 + n)`, EVERY `n`.** -/
theorem ha_img_W3 : ∀ (n : ℕ) (v : Ordinal.{0}), v ≤ haW3 ρ n → GnI ρ δ v
  | 0 => fun v hv => ha_img_le_B3 h (by rw [← haW3_zero h.ρE h.ρ1]; exact hv)
  | n + 1 => by
    have hρE := h.ρE
    have hρ1 := h.ρ1
    obtain ⟨hPf, hρP, -⟩ := haW3_facts hρE hρ1 n
    obtain ⟨-, -, hNq'⟩ := haW3_facts hρE hρ1 (n + 1)
    have hN : haW3 ρ (n + 1) = haN (haW3 ρ n) := haW3_succ hρE hρ1 n
    have hNq : haN (haW3 ρ n) < gq 1 ρ := hN ▸ hNq'
    have hlt : ∀ v, v < haW3 ρ (n + 1) → GnI ρ δ v := fun v hv =>
      ha_img_next h hPf hρP hNq (ha_img_W3 n) v (hN ▸ hv)
    intro v hv
    rcases hv.lt_or_eq with hv | rfl
    · exact hlt v hv
    · exact ha_img_W3succ h n hlt

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION UP TO `φ(3, Γ_{ρ+1} + 1 + n)`.** -/
theorem ha_pkg_W3 {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (n : ℕ) (hT : T ρ ≤ haW3 ρ n) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (ha_img_W3 h n _ hT) hex

end ImgW3

end Googology.Trans.PoR.InaccPsi.R2.Ha
