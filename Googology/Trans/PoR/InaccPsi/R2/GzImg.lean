import Googology.Trans.PoR.InaccPsi.R2.GzN

/-!
# LEMMA IMG AT THE LIMIT `ε`-FIXED POINTS, AND FOR EVERY VALUE BELOW `B₃(ρ)` (the least `φ(2,·)`-fixed point above
`ζ_{Γ_{ρ+1}+1}`)

`Gw.gwImg_Zn` gives Lemma IMG below every `ζ_{Γ_{ρ+1}+n}` (successor `ε`-fixed points, `Gw.gwI_fixZ`).  Here the limit
`ε`-fixed points `E = ζ_{Γ_{ρ+1}+λ}` (`λ` a limit):

* `gz_i0_le`, `gz_i0_lt`, `gz_Z1_notfix`, `gz_glA2V` (**`ϑˣ(Ω₁·2 + Γ_{x+1} + ν) = φ(2, i₀ + ν)`**, `φ(2, i₀) =
  ζ_{Γ_{x+1}+1}`, as long as no `φ(2,·)`-fixed point is passed);
* `gz_floor` (every ordinal above a `ζ`-number lies in some `[φ(2, j), φ(2, j+1))`), `gz_lg_add` (`lg(a+b) = lg b`),
  `gz_glZeta_le`, `gz_glZeta_eq`;
* `gzI_limZ` (**LEMMA IMG AT A LIMIT `ε`-FIXED POINT `E = φ(2, i₀ + c)`, `c` a limit**, given Lemma IMG below `E`:
  the source `E ≤₁ E·3 + z` (`z = lg c`, `Gl.gl_lh_th` at the ϑ-index `Γ_{ρ+1} + c`) is copied to
  `f(E) ≤₁ f(E)·3 + f(z)`; a copy with `f(E) < π(E)` gives an `ε`-number `u ∈ (φ(2, i₀ + c'), E)` with `π(u) = f(E)`,
  `c = c' + ω^z`; by `π(lh(u)) = lh(π(u))` ([W07b] Cor 5.7, `lh_pi`), `lh(u) ≥ u·3 + z`; if `u` is not an `ε`-fixed
  point then `lh(u) = u·2 + lg(d)` (`Gk.gk_lh_evA` above the `ε`-fixed point below `u`), too small; if `u = φ(2, i₀+d)`
  then `lh(u) ≤ u·3 + lg(d)`, so `ω^z ∣ d` with `c' < d < c' + ω^z`, impossible);
* `gzB3` (**`B₃(x)`**, the least fixed point of `φ(2, ·)` above `ζ_{Γ_{x+1}+1}`), `gzB3_fix`, `gzB3_E`, `gzZ1_lt_B3`,
  `gz_fix_ge_B3`, `gzB3_lt1` (`B₃(x) < Γ_{x+2}`, through `ϑˣ(Ω₁·3 + Γ_{x+1})`);
* `gzImg_B3` (**LEMMA IMG FOR EVERY VALUE BELOW `B₃(ρ)`**: every `ε`-fixed point `ζ_{Γ_{ρ+1}+ν}` with successor or
  limit index, and every `ε`-number between), `gzPkg_of_exB3` (**Lemma IMG (gated) for a specified function with
  Lemma EXACT and value below `B₃(ρ)`**).

No new axiom.  New definition: `gzB3`.

[W07b] G. Wilken, "Σ1-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gz

open Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Ordinal facts -/

/-- **Every ordinal above a `ζ`-number lies in some `[φ(2, j), φ(2, j+1))`.** -/
theorem gz_floor {u j0 : Ordinal.{0}} (h0 : veblen 2 j0 ≤ u) : ∃ j, veblen 2 j ≤ u ∧ u < veblen 2 (j + 1) := by
  have hne : ({j | u < veblen 2 j} : Set Ordinal.{0}).Nonempty :=
    ⟨u + 1, (lt_add_one u).trans_le (right_le_veblen 2 _)⟩
  have hmS : u < veblen 2 (sInf {j | u < veblen 2 j}) := csInf_mem hne
  have hmin : ∀ j, j < sInf {j | u < veblen 2 j} → veblen 2 j ≤ u := fun j hj =>
    not_lt.1 (fun h => absurd (csInf_le' (s := {j | u < veblen 2 j}) h) (not_le.2 hj))
  rcases zero_or_succ_or_isSuccLimit (sInf {j | u < veblen 2 j}) with h0' | ⟨j, hj⟩ | hlim
  · exfalso
    rw [h0'] at hmS
    exact absurd (((isNormal_veblen 2).monotone zero_le).trans h0) (not_le.2 hmS)
  · have hj' : sInf {j | u < veblen 2 j} = j + 1 := by rw [← hj, Order.succ_eq_add_one]
    exact ⟨j, hmin j (by rw [hj']; exact lt_add_one j), by rw [← hj']; exact hmS⟩
  · exfalso
    obtain ⟨a, ha, hua⟩ := ((isNormal_veblen 2).lt_iff_exists_lt hlim).1 hmS
    exact absurd (hmin a ha) (not_le.2 hua)

/-- **`lg(a + b) = lg(b)`** for `b ≠ 0`. -/
theorem gz_lg_add (a : Ordinal.{0}) {b : Ordinal.{0}} (hb : b ≠ 0) : lg (a + b) = lg b := by
  obtain ⟨b', hb', hdvd, -⟩ := lg_split hb
  obtain ⟨m, hm⟩ := lg_dvd hb
  set w := lg b with hw
  have hp : (0 : Ordinal.{0}) < ω ^ w := opow_pos _ omega0_pos
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hm; exact hb hm
  have hab : a % ω ^ w + b = b := by
    obtain ⟨m', hm'⟩ : ∃ m', m = 1 + m' :=
      ⟨m - 1, (Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hm0)).symm⟩
    rw [hm, hm', mul_add, mul_one, ← add_assoc,
      (isPrincipal_add_omega0_opow w).add_eq_right (Ordinal.mod_lt a hp.ne')]
  have e : a + b = (ω ^ w * (a / ω ^ w) + b') + ω ^ w := by
    conv_lhs => rw [← Ordinal.div_add_mod a (ω ^ w)]
    rw [add_assoc, hab, hb', add_assoc]
  rw [e]
  exact lg_add_opow (dvd_add (dvd_mul_right _ _) hdvd)

theorem gz_glZeta_le (τ t : Ordinal.{0}) (k : ℕ) : glZeta τ k t ≤ lg t := by
  unfold glZeta
  split_ifs
  · exact le_rfl
  · exact zero_le

theorem gz_glZeta_eq {τ t : Ordinal.{0}} {k : ℕ} (ht : t ≠ 0)
    (hσ : ∃ σ, σ < t ∧ t < vt τ (Om1 * (k : Ordinal.{0}) + σ)) : glZeta τ k t = lg t := by
  unfold glZeta; rw [if_pos ⟨ht, hσ⟩]

theorem gz_vt2 (σ x : Ordinal.{0}) : vt x (Om1 * ((2 : ℕ) : Ordinal.{0}) + σ) = glA 2 σ x := by
  rw [Nat.cast_ofNat]; rfl

theorem gz_mul3 (a : Ordinal.{0}) : a * ((2 + 1 : ℕ) : Ordinal.{0}) = a + a + a := by
  rw [vz_mul_three, mul_two_eq]

/-! ## Level-2 readings over the pseudo-base `Γ_{x+1}` -/

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gz_i0_le {i0 : Ordinal.{0}} (hi0 : veblen 2 i0 = evZ (lgG x)) : i0 ≤ lgG x + 1 := by
  have h : evZ (lgG x) ≤ veblen 2 (lgG x + 1) :=
    evZ_le ((lt_add_one _).trans_le (right_le_veblen 2 _)) (veblen_veblen_of_lt one_lt_two _)
  rw [← hi0] at h
  exact (isNormal_veblen 2).strictMono.le_iff_le.1 h

theorem gz_i0_lt {i0 : Ordinal.{0}} (hi0 : veblen 2 i0 = evZ (lgG x)) : i0 < evZ (lgG x) :=
  (gz_i0_le hx hx1 hi0).trans_lt ((ev_isSuccLimit_of_inE (evZ_E _)).add_one_lt (lt_evZ _))

/-- **`ζ_{Γ_{x+1}+1}` is not a fixed point of `φ(2, ·)`.** -/
theorem gz_Z1_notfix : veblen 2 (evZ (lgG x)) ≠ evZ (lgG x) := by
  obtain ⟨i0, hi0⟩ := gw_LuP2 (lgG x)
  intro e
  have h := (isNormal_veblen 2).strictMono (gz_i0_lt hx hx1 hi0)
  rw [hi0, e] at h
  exact lt_irrefl _ h

/-- **`ϑˣ(Ω₁·2 + Γ_{x+1} + ν) = φ(2, i₀ + ν)`** (`φ(2, i₀) = ζ_{Γ_{x+1}+1}`) for every `ν` with
`Γ_{x+1} + ν < Γ_{x+2}` and no `φ(2,·)`-fixed point `i₀ + ν'`, `ν' ≤ ν` a limit. -/
theorem gz_glA2V {i0 : Ordinal.{0}} (hi0 : veblen 2 i0 = evZ (lgG x)) : ∀ ν, lgG x + ν < gq 1 x →
    (∀ ν', ν' ≤ ν → IsSuccLimit ν' → i0 + ν' < veblen 2 (i0 + ν')) →
    glA 2 (lgG x + ν) x = veblen 2 (i0 + ν) := by
  obtain ⟨h2T, h21⟩ := gw_two_T hx hx1
  have h12 : (1 : Ordinal.{0}) ≤ 2 := one_le_two
  obtain ⟨hGT, hG1⟩ := gm1_T hx hx1 (mg_lgG_lt_G1 hx hx1)
  have hG0 : glA 2 (lgG x) x = veblen 2 i0 := by rw [hi0]; exact gw_glA2_eq hx hx1
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hq hfix
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 hq
  rcases Ordinal.zero_or_succ_or_isSuccLimit ν with h0 | ⟨d, hd⟩ | hlim
  · subst h0; rw [add_zero, add_zero]; exact hG0
  · have hd' : ν = d + 1 := by rw [← succ_eq_add_one]; first | exact hd | exact hd.symm
    subst hd'
    have hdq : lgG x + d < gq 1 x := lt_of_le_of_lt (add_le_add le_rfl le_self_add) hq
    have IHd := IH d (lt_add_one d) hdq (fun ν' h hl => hfix ν' (h.trans le_self_add) hl)
    rw [← add_assoc] at hq ⊢
    rw [gz_glA2_succ hx hx1 hq, IHd, ← add_assoc, gz_evZ_veb2]
  · have hval : ∀ ν'', ν'' < ν → glA 2 (lgG x + ν'') x = veblen 2 (i0 + ν'') := fun ν'' h =>
      IH ν'' h ((add_lt_add_iff_left _).2 h |>.trans hq) (fun ν' h' hl => hfix ν' (h'.trans h.le) hl)
    set u := veblen 2 (i0 + ν) with hu
    have huE : InE u := gg_veblen_eps two_ne_zero
    have hiu : veblen 2 i0 < u := (isNormal_veblen 2).strictMono (lt_add_of_pos_right _ hlim.bot_lt)
    obtain ⟨-, hxa, -, -, h2a, hGa⟩ := glA_facts hx hx1 h12 h2T h21 hGT hG1
    rw [hG0] at hxa h2a hGa
    have htu : lgG x + ν < u := (inE_indec huE).add_lt (hGa.trans hiu)
      ((le_add_self : ν ≤ i0 + ν).trans_lt (hfix ν le_rfl hlim))
    refine le_antisymm ?_ ?_
    · refine glA_min hx hx1 h12 h2T h21 htT ht1 ⟨_, rfl⟩ (hxa.trans hiu) htu (h2a.trans hiu) (fun σ hσ => ?_)
      rcases lt_or_ge σ (lgG x) with hσP | hσP
      · obtain ⟨hσT, hσ1⟩ := gm1_T hx hx1 (hσP.trans (mg_lgG_lt_G1 hx hx1))
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
        have hq' : lgG x + c' < gq 1 x := ((add_lt_add_iff_left _).2 hc').trans hq
        obtain ⟨hcT, -⟩ := gm1_T hx hx1 hq'
        rw [← hval c' hc']
        exact (glA_lt_of hx hx1 h12 h2T h21 hcT htT ht1 ((add_lt_add_iff_left _).2 hc')).le

end Base

/-! ## `B₃(x)`: the least fixed point of `φ(2, ·)` above `ζ_{Γ_{x+1}+1}` -/

/-- **`B₃(x)`**, the least fixed point of `φ(2, ·)` above `ζ_{Γ_{x+1}+1}` (`= φ(3, Γ_{x+1} + 1)`). -/
noncomputable def gzB3 (x : Ordinal.{0}) : Ordinal.{0} := nfp (veblen 2) (evZ (lgG x) + 1)

theorem gzB3_fix (x : Ordinal.{0}) : veblen 2 (gzB3 x) = gzB3 x := nfp_fp (isNormal_veblen 2) _

theorem gzZ1_lt_B3 (x : Ordinal.{0}) : evZ (lgG x) < gzB3 x := (lt_add_one _).trans_le (le_nfp _ _)

theorem gzB3_E (x : Ordinal.{0}) : InE (gzB3 x) := by
  have h : ω ^ veblen 2 (gzB3 x) = veblen 2 (gzB3 x) := gg_veblen_eps two_ne_zero
  rw [gzB3_fix] at h; exact h

/-- **Every fixed point of `φ(2, ·)` above `ζ_{Γ_{x+1}+1}` is at least `B₃(x)`.** -/
theorem gz_fix_ge_B3 {x j : Ordinal.{0}} (hj : veblen 2 j = j) (hZj : evZ (lgG x) < j) : gzB3 x ≤ j :=
  nfp_le_fp (isNormal_veblen 2).strictMono.monotone (Order.add_one_le_of_lt hZj) hj.le

section B3

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`B₃(x) < Γ_{x+2}`**: `ϑˣ(Ω₁·3 + Γ_{x+1})` is a fixed point of `φ(2, ·)` above `ζ_{Γ_{x+1}+1}`, below `Γ_{x+2}`. -/
theorem gzB3_lt1 : gzB3 x < gq 1 x := by
  obtain ⟨hGT, -, hG1, -, -⟩ := lgG_facts hx hx1
  have hq := (gm1_facts hx hx1).2.2.2
  have h3q : (3 : Ordinal.{0}) < gq 1 x := (natCast_lt_omega0 3).trans (omega0_lt_inE hq)
  obtain ⟨h3T, h31⟩ := gm1_T hx hx1 h3q
  have h13 : (1 : Ordinal.{0}) ≤ 3 := by norm_num
  obtain ⟨-, -, -, -, -, hta⟩ := glA_facts hx hx1 h13 h3T h31 hGT hG1
  obtain ⟨k, hk⟩ := glA_P hx hx1 h13 h3T h31 hGT hG1
  have hfix2 : veblen 2 (glA 3 (lgG x) x) = glA 3 (lgG x) x := by
    rw [← hk]; exact veblen_veblen_of_lt (by norm_num) k
  have hfix1 : Ordinal.epsilon (glA 3 (lgG x) x) = glA 3 (lgG x) x := by
    rw [← hk]; exact veblen_veblen_of_lt (by norm_num) k
  have hZ : evZ (lgG x) ≤ glA 3 (lgG x) x := evZ_le hta hfix1
  have hne : evZ (lgG x) ≠ glA 3 (lgG x) x := fun e => gz_Z1_notfix hx hx1 (by rw [e]; exact hfix2)
  exact (gz_fix_ge_B3 hfix2 (lt_of_le_of_ne hZ hne)).trans_lt
    (lgVt_lt_low hx hx1 h3T h31 hGT hG1 (gm1_one_T hx hx1).1 (gm1_one_T hx hx1).2 h3q (mg_lgG_lt_G1 hx hx1))

/-- Below `B₃(x)` no index `j ≥ i₀` is a fixed point of `φ(2, ·)`. -/
theorem gz_nofix_B3 {i0 j : Ordinal.{0}} (hi0 : veblen 2 i0 = evZ (lgG x)) (hij : i0 ≤ j)
    (hjB : veblen 2 j < gzB3 x) : j < veblen 2 j := by
  rcases (right_le_veblen 2 j).lt_or_eq with h | h
  · exact h
  · exfalso
    have hZj : evZ (lgG x) ≤ j := by
      rw [← hi0, h]; exact (isNormal_veblen 2).monotone hij
    have hne : evZ (lgG x) ≠ j := fun e => gz_Z1_notfix hx hx1 (by rw [e]; exact h.symm)
    have := gz_fix_ge_B3 h.symm (lt_of_le_of_ne hZj hne)
    rw [h] at this
    exact absurd hjB (not_lt.2 this)

end B3

/-! ## Lemma IMG at a limit `ε`-fixed point -/

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG AT A LIMIT `ε`-FIXED POINT `E = φ(2, i₀ + c)`** (`φ(2, i₀) = ζ_{Γ_{ρ+1}+1}`, `c` a limit, `Γ_{ρ+1} + c <
Γ_{ρ+2}`, no `φ(2,·)`-fixed point `i₀ + ν'`, `ν' ≤ c`), given Lemma IMG for every value below `E`. -/
theorem gzI_limZ {i0 c : Ordinal.{0}} (hi0 : veblen 2 i0 = evZ (lgG ρ)) (hlim : IsSuccLimit c)
    (hq : lgG ρ + c < gq 1 ρ) (hfix : ∀ ν', ν' ≤ c → IsSuccLimit ν' → i0 + ν' < veblen 2 (i0 + ν'))
    (IH : ∀ u, u < veblen 2 (i0 + c) → GnI ρ δ u) : GnI ρ δ (veblen 2 (i0 + c)) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hc0 : c ≠ 0 := hlim.bot_lt.ne'
  have hEv : glA 2 (lgG ρ + c) ρ = veblen 2 (i0 + c) := gz_glA2V hρE hρ1 hi0 c hq hfix
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
  -- the reach `lh(E) = E·3 + z`
  have hlhE : IsLh1 E (E + E + E + z) := by
    have hL := gl_lh_th (k := 2) hρE hρ1 (by norm_num) htT ht1
    have hz' : glZeta ρ 2 (lgG ρ + c) = z := by
      rw [gz_glZeta_eq (lt_of_lt_of_le hlim.bot_lt (le_add_self : c ≤ lgG ρ + c)).ne' ?_, gz_lg_add _ hc0]
      obtain ⟨a, ha, hta⟩ := ((isNormal_veblen 2).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 htE
      have hc'' : a - i0 < c := by
        rcases lt_or_ge a i0 with hai | hai
        · rw [Ordinal.sub_eq_zero_iff_le.2 hai.le]; exact hlim.bot_lt
        · have : i0 + (a - i0) < i0 + c := by rw [Ordinal.add_sub_cancel_of_le hai]; exact ha
          exact (add_lt_add_iff_left _).1 this
      refine ⟨lgG ρ + (a - i0), (add_lt_add_iff_left _).2 hc'', ?_⟩
      have hq'' : lgG ρ + (a - i0) < gq 1 ρ := ((add_lt_add_iff_left _).2 hc'').trans hq
      rw [gz_vt2, gz_glA2V hρE hρ1 hi0 _ hq'' (fun ν' h' hl => hfix ν' (h'.trans hc''.le) hl)]
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
  have hZE' : evZ (lgG ρ) ≤ E' := by rw [← hi0]; exact (isNormal_veblen 2).monotone le_self_add
  have hρu : ρ < u := (((lgG_facts hρE hρ1).2.1.trans (lt_evZ _)).trans_le hZE').trans hE'u
  obtain ⟨l, hl, hlTB, hpl⟩ := lh_pi hB huTB hρu hu1
  obtain ⟨huu1, huu2⟩ := pi_add hB huTB huTB
  have hle0 := hpl.2 _ (by rw [hpu]; exact hR)
  obtain ⟨j, hj1, hj2⟩ := gz_floor (j0 := i0 + c') hE'u.le
  rcases hj1.lt_or_eq with hju | hju
  · -- `u` is not an `ε`-fixed point: `lh(u) = u·2 + lg(d)` is too small
    have hZE : InE (veblen 2 j) := gg_veblen_eps two_ne_zero
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
  · -- `u = φ(2, i₀ + d)`, `c' < d < c`: `lh(u) ≤ u·3 + lg(d)` forces `ω^z ∣ d`
    have hj' : i0 + c' < j := by
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
    have hqd : lgG ρ + d < gq 1 ρ := ((add_lt_add_iff_left _).2 hdc).trans hq
    obtain ⟨hdT, hd1⟩ := gm1_T hρE hρ1 hqd
    have hL := gl_lh_th (k := 2) hρE hρ1 (by norm_num) hdT hd1
    rw [gz_vt2, gz_glA2V hρE hρ1 hi0 d hqd (fun ν' h' hl => hfix ν' (h'.trans hdc.le) hl), hju,
      gz_mul3] at hL
    have hζlg : glZeta ρ 2 (lgG ρ + d) ≤ lg d := (gz_glZeta_le ρ (lgG ρ + d) 2).trans (gz_lg_add _ hd0).le
    have hl' : l = u + u + u + glZeta ρ 2 (lgG ρ + d) := lkcIsLh1_unique hl hL
    rw [hl'] at hlTB hle0
    have huuu1 : u + u + u < Om1 :=
      (inE_indec gl_Om1_E).add_lt ((inE_indec gl_Om1_E).add_lt hu1 hu1) hu1
    have hζ1 : glZeta ρ 2 (lgG ρ + d) < Om1 := hζlg.trans_lt ((lg_le hd0).trans_lt (hdc.trans (hcE.trans hET.2)))
    have hlg1 : u + u + u + glZeta ρ 2 (lgG ρ + d) < Om1 := (inE_indec gl_Om1_E).add_lt huuu1 hζ1
    obtain ⟨huuu, huuu2⟩ := pi_add hB huu1 huTB
    obtain ⟨hζTB, -⟩ := TB_sub hB huuu hlTB le_self_add hlg1
    rw [Ordinal.add_sub_cancel] at hζTB
    obtain ⟨-, hps⟩ := pi_add hB huuu hζTB
    rw [hps, huuu2, huu2, hpu] at hle0
    have hfz : f z ≤ pi (f ρ) ρ (glZeta ρ 2 (lgG ρ + d)) := (add_le_add_iff_left _).1 hle0
    have hzζ : z ≤ glZeta ρ 2 (lgG ρ + d) := ((pi_bijOn hB).2.le_iff_le hzTB hζTB).1 (pz.trans hfz)
    have hdiv : ω ^ z ∣ d := (le_lg_iff hd0 z).1 (hzζ.trans hζlg)
    obtain ⟨δ', hδ'⟩ : ∃ δ', d = c' + δ' := ⟨d - c', (Ordinal.add_sub_cancel_of_le hc'd.le).symm⟩
    have hδ0 : δ' ≠ 0 := by rintro rfl; rw [add_zero] at hδ'; exact absurd hδ' hc'd.ne'
    have hδlt : δ' < ω ^ z := by
      have : c' + δ' < c' + ω ^ z := by rw [← hδ', ← hcs]; exact hdc
      exact (add_lt_add_iff_left _).1 this
    have hdivδ : ω ^ z ∣ δ' := (dvd_add_iff hdvd).1 (by rw [← hδ']; exact hdiv)
    exact absurd (Ordinal.le_of_dvd hδ0 hdivδ) (not_le.2 hδlt)

/-- **LEMMA IMG FOR EVERY VALUE BELOW `B₃(ρ)`** (the least `φ(2,·)`-fixed point above `ζ_{Γ_{ρ+1}+1}`): every
`ε`-fixed point `ζ_{Γ_{ρ+1}+ν}` (successor index: `Gw.gwI_fixZ`; limit index: `gzI_limZ`) and every `ε`-number
between two of them (`Gw.gwI_epsP`). -/
theorem gzImg_B3 : ∀ v, v < gzB3 ρ → GnI ρ δ v := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨i0, hi0⟩ := gw_LuP2 (lgG ρ)
  have hB3q := gzB3_lt1 hρE hρ1
  obtain ⟨-, hρG, -, hGE, -⟩ := lgG_facts hρE hρ1
  have hρZ : ρ < evZ (lgG ρ) := hρG.trans (lt_evZ _)
  refine gnImg_of_eps h (fun v hv => gm1_T hρE hρ1 (hv.trans hB3q)) (fun e he _ heB IHe => ?_)
  rcases lt_trichotomy e (evZ (lgG ρ)) with hlt | heq | hgt
  · exact gnImg_Z h e hlt
  · rw [heq]; exact gwI_fixZ h hGE hρG (mg_lgG_lt_G1 hρE hρ1) (gnImg_Z h)
  · obtain ⟨j, hj1, hj2⟩ := gz_floor (u := e) (j0 := i0) (by rw [hi0]; exact hgt.le)
    have hi0j : i0 ≤ j := by
      have : veblen 2 i0 < veblen 2 (j + 1) := by rw [hi0]; exact hgt.trans hj2
      exact Order.lt_add_one_iff.1 ((isNormal_veblen 2).strictMono.lt_iff_lt.1 this)
    have hZj : evZ (lgG ρ) ≤ veblen 2 j := by rw [← hi0]; exact (isNormal_veblen 2).monotone hi0j
    rcases hj1.lt_or_eq with hjlt | hjeq
    · exact gwI_epsP h (gg_veblen_eps two_ne_zero) (hρZ.trans_le hZj) (hjlt.trans (heB.trans hB3q)) he hjlt
        (by rw [gz_evZ_veb2]; exact hj2) IHe
    · obtain ⟨d, rfl⟩ := exists_add_of_le hi0j
      rcases zero_or_succ_or_isSuccLimit d with h0 | ⟨d', hd'⟩ | hlim
      · subst h0
        rw [add_zero, hi0] at hjeq
        exact absurd hjeq hgt.ne
      · have e1 : i0 + d = (i0 + d') + 1 := by rw [← hd', succ_eq_add_one, add_assoc]
        rw [e1, ← gz_evZ_veb2] at hjeq
        subst hjeq
        have hZd' : evZ (lgG ρ) ≤ veblen 2 (i0 + d') := by
          rw [← hi0]; exact (isNormal_veblen 2).monotone le_self_add
        exact gwI_fixZ h (gg_veblen_eps two_ne_zero) (hρZ.trans_le hZd') ((lt_evZ _).trans (heB.trans hB3q)) IHe
      · subst hjeq
        have hnf : ∀ ν', ν' ≤ d → i0 + ν' < veblen 2 (i0 + ν') := fun ν' h' =>
          gz_nofix_B3 hρE hρ1 hi0 le_self_add
            (((isNormal_veblen 2).monotone ((add_le_add_iff_left _).2 h')).trans_lt heB)
        have hq : lgG ρ + d < gq 1 ρ :=
          (inE_indec (gm1_facts hρE hρ1).2.2.2).add_lt (mg_lgG_lt_G1 hρE hρ1)
            (((le_add_self : d ≤ i0 + d).trans_lt (hnf d le_rfl)).trans (heB.trans hB3q))
        exact gzI_limZ h hi0 hlim hq (fun ν' h' _ => hnf ν' h') IHe

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW `B₃(ρ)`**: Lemma EXACT above the gate `g < ρ` with constants
`C < ρ` and `T(ρ) < B₃(ρ)` give `T(f ρ) ≤ f(T ρ)` for every covering copy `f` that keeps `g`. -/
theorem gzPkg_of_exB3 {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : T ρ < gzB3 ρ) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (gzImg_B3 h _ hT) hex

end Img

end Googology.Trans.PoR.InaccPsi.R2.Gz
