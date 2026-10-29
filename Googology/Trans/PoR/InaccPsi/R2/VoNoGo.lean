import Googology.Trans.PoR.InaccPsi.R2.VoForm

/-!
# The decomposition road hypothesis fails at every `L(k)`

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Let `a = L(k)` (a `υ`-fixed restart), `c = ω^{υ_{a+1}+1}`, `g = ω^c`, `λ = a + g`, `ν = λ + ω²`.  The name of `λ`
is `η_a + g`, so its code is `c`, its reading is `c` (`c ≤ ρ_λ`), and `r(λ) = δ_λ + c` (`Ra.raR_low`).  No restart
in `(a, ν)` has a reach above `ρ_ν` (all their codes are `≤` their offsets), so `ν` is an uncovered Range restart,
isolated from below, in the window `[υ(a + c_ω(a)), L(k+1))`.  Every `β` with `ρ_ν < υ_{a+β}` has `g` as an inner
offset, and at `g` none of the three forms holds (`Vo.voForms_fail`).  So `Vl.VlGdTyVis` is false at `a`.

* `voCode_add` (the codes of `a + z`, `ω ≤ z < υ_{a+2}`), `voR_low` (`r(a + z) = δ + m_{a+z}` with `m_{a+z} ≤ z`);
* `voNoGo` (**`¬ VlGdTyVis S L(k) L(k+1) (υ(L(k) + c_ω(L(k)))) w` for every `w`, given `L(k+1) ≤ ν_C`**);
* `voNoGo_n`, `voNoGo_0` (the hypotheses `hn n`, `h0` of `Vl.vlGdTyRoad` are false), `voNoGo_road` (**under the
  section hypotheses `hU, hV, hVt, hL` of the road, both are false: `Vl.vlGdTyRoad` is vacuous**);
* `voNoGo_uy`, `voNoGo_ur`, `voNoGo_un` (the same for `Uy.UyGdTyVis`, `Ur.UrGdTyVis`, `Un.UnGdTyVis`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vo

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Tk Googology.Trans.PoR.InaccPsi.R2.Ub
  Googology.Trans.PoR.InaccPsi.R2.Vl

variable {S : InaccSeq.{0}}

/-- An `ε`-number `e > 0` is at least `ω`. -/
theorem vo_omega_le {e : Ordinal.{0}} (he : InE e) (h0 : 0 < e) : ω ≤ e :=
  calc ω ≤ ω ^ e := left_le_opow ω h0
    _ = e := he

/-- `ω^2` with a natural exponent is `ω^2` with an ordinal exponent. -/
theorem vo_e2 : (ω ^ 2 : Ordinal.{0}) = ω ^ (2 : Ordinal.{0}) := by simpa using (opow_natCast ω 2).symm

/-- `ω + 2 < ω²`. -/
theorem vo_om2 : ω + 2 < (ω ^ 2 : Ordinal.{0}) := by
  rw [vo_e2]
  have hp : IsPrincipal (· + ·) (ω ^ (2 : Ordinal.{0})) := isPrincipal_add_omega0_opow 2
  have h1 : ω < ω ^ (2 : Ordinal.{0}) := by
    calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
      _ < ω ^ (2 : Ordinal.{0}) := (opow_lt_opow_iff_right one_lt_omega0).2 one_lt_two
  have h2 : (2 : Ordinal.{0}) < ω ^ (2 : Ordinal.{0}) := (natCast_lt_omega0 2).trans h1
  exact hp h1 h2

/-- **The codes above `a = L(k)`**: `m_{a+z} = -1 + e(z)` for `ω ≤ z < υ_{a+2}` (the name is `η_a + z`). -/
theorem voCode_add (k : ℕ) {z : Ordinal.{0}} (hz : ω ≤ z) (hzu : z < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2)) :
    cdCode S (Nc.ncL S (k : Ordinal.{0}) + z) = cdOff (cdExp z) := by
  have hm := upsilon_normal.strictMono
  set l := Nc.ncL S (k : Ordinal.{0})
  set L1 := Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})
  have hl0 : 0 < l := pos_iff_ne_zero.2 (Te.teRst_L (S := S) k).1
  have hL1fix : upsilon L1 = L1 := Te.teUps_L (k + 1)
  have hL1E : InE L1 := hL1fix ▸ upsPt_inE (upsPt_upsilon (hl0.trans (Te.teL_lt_succ k)))
  have h2 : (2 : Ordinal.{0}) < L1 :=
    (natCast_lt_omega0 2).trans_le (vo_omega_le hL1E (hl0.trans (Te.teL_lt_succ k)))
  have hl2 : l + 2 < L1 := hL1E.add_lt (Te.teL_lt_succ k) h2
  have hn : upsilon (l + 2) < Nm.Pv S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) := by
    have h := hm hl2; rw [hL1fix] at h; rw [← Lw.lw_L_eq]; exact h
  have e2 : (2 : Ordinal.{0}) + z = z := by
    have := natCast_add_of_omega0_le hz 2; simpa using this
  have e : l + z = l + 2 + z := by rw [add_assoc, e2]
  have hz0 : z ≠ 0 := (omega0_pos.trans_le hz).ne'
  rw [e]
  exact Cp.cpCode_add (ne_of_gt (hl0.trans_le le_self_add)) hn hzu hz0

/-- **The reach of a low-code restart `λ`**: if `m_λ ≤ ρ_λ` and `υ_{λ+ω+1} < ν_C` then `r(λ) = δ_λ + m_λ`. -/
theorem voR_low {lam : Ordinal.{0}} (hl : IsRestartIdx lam) (hC : upsilon (lam + ω + 1) < nuC)
    (hm : cdCode S lam ≤ upsilon lam) : cdR S lam = cdDelta lam + cdCode S lam := by
  have hθ : cdTheta S lam (cdCode S lam) = cdCode S lam := cdTheta_small S hm
  have h := Ra.raR_low hl hC (by rw [hθ]; exact hm.trans_lt (cdRho_lt_delta lam))
  rw [h, hθ]

/-- WIT(k): **the witness at `a = L(k)`** (given `L(k+1) ≤ ν_C`): the Range restart `ν = a + g + ω²`
(`g = ω^c`, `c = ω^e`, `e = υ_{a+1} + 1`) is in the window `[υ(a + c_ω(a)), L(k+1))`, uncovered and isolated
from below, every `β` with `ρ_ν < υ_{a+β}` has `g < β`, `g + ω + 2 ≤ β`, and `r(a + g) = υ_{a+(g+ω+1)} + c` with
`c` additive principal, not an `ε`-number, `υ_{a+1} ≤ c < υ_{a+(g+ω+1)} < Ω₁`. -/
theorem voWit (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) :
    ∃ ν g e : Ordinal.{0}, CdRange S ν ∧
      upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0}))) ≤ upsilon ν ∧
      upsilon ν < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧ upsilon (Nc.ncL S (k : Ordinal.{0})) < upsilon ν ∧
      ¬ TkCov S (upsilon (Nc.ncL S (k : Ordinal.{0}))) ν ∧ TkIso S (upsilon (Nc.ncL S (k : Ordinal.{0}))) ν ∧
      0 < g ∧ ω ^ 2 ∣ g ∧
      (∀ β, upsilon ν < upsilon (Nc.ncL S (k : Ordinal.{0}) + β) → g < β ∧ g + ω + 2 ≤ β) ∧
      cdR S (Nc.ncL S (k : Ordinal.{0}) + g) = upsilon (Nc.ncL S (k : Ordinal.{0}) + (g + ω + 1)) + ω ^ e ∧
      ω ^ e ∈ NonEAP ∧ upsilon (succ (Nc.ncL S (k : Ordinal.{0}))) ≤ ω ^ e ∧
      ω ^ e < upsilon (Nc.ncL S (k : Ordinal.{0}) + (g + ω + 1)) ∧
      upsilon (Nc.ncL S (k : Ordinal.{0}) + (g + ω + 1)) < Om1 ∧ 0 < Nc.ncL S (k : Ordinal.{0}) := by
  have hm := upsilon_normal.strictMono
  set l := Nc.ncL S (k : Ordinal.{0}) with hldef
  set L1 := Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) with hL1def
  have hlfix : upsilon l = l := Te.teUps_L k
  have hL1fix : upsilon L1 = L1 := Te.teUps_L (k + 1)
  have hlR : IsRestartIdx l := Te.teRst_L k
  have hl0 : 0 < l := pos_iff_ne_zero.2 hlR.1
  have hlL1 : l < L1 := Te.teL_lt_succ k
  have hL1O : L1 < Om1 := by rw [hL1def, Lw.lw_L_eq, Br.Om1_eq]; exact Nm.Pv_lt_Om1 S _
  have hL1E : InE L1 := hL1fix ▸ upsPt_inE (upsPt_upsilon (hl0.trans hlL1))
  have hlE : InE l := hlfix ▸ upsPt_inE (upsPt_upsilon hl0)
  have hbelow : ∀ x, x < L1 → upsilon x < L1 := fun x hx => hL1fix ▸ hm hx
  have hωL1 : ω < L1 := (vo_omega_le hlE hl0).trans_lt hlL1
  have hnatL1 : ∀ n : ℕ, (n : Ordinal.{0}) < L1 := fun n => (natCast_lt_omega0 n).trans hωL1
  have hC : ∀ x, x < L1 → upsilon (x + ω + 1) < nuC := fun x hx =>
    (hbelow _ (hL1E.add_lt (hL1E.add_lt hx hωL1) (by exact_mod_cast hnatL1 1))).trans_le hν
  -- the constants
  set u1 := upsilon (l + 1) with hu1
  set u2 := upsilon (l + 2) with hu2
  have hu1P : 0 < u1 := (upsPt_upsilon (hl0.trans_le le_self_add)).1
  have hu2E : InE u2 := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
  have hu12 : u1 < u2 := hm ((add_lt_add_iff_left l).2 one_lt_two)
  have hlu1 : l < u1 := hlfix ▸ hm (lt_add_one l)
  have hu2L1 : u2 < L1 := hbelow _ (hL1E.add_lt hlL1 (by exact_mod_cast hnatL1 2))
  set c := ω ^ (u1 + 1) with hc
  set g := ω ^ c with hg
  have hcu2 : c < u2 :=
    hu2E.opow_lt (hu2E.add_lt hu12 ((Order.one_le_iff_pos.2 hu1P).trans_lt hu12))
  have hgu2 : g < u2 := hu2E.opow_lt hcu2
  have hωc : ω ≤ c := left_le_opow ω (lt_of_le_of_lt zero_le (lt_add_one u1))
  have h2c : (2 : Ordinal.{0}) ≤ c := ((natCast_lt_omega0 2).trans_le hωc).le
  have hω2g : ω ^ 2 ∣ g := vo_e2 ▸ opow_dvd_opow ω h2c
  have hω2le : ω ^ 2 ≤ g := vo_e2 ▸ opow_le_opow_right omega0_pos h2c
  have hcg : c ≤ g := right_le_opow c one_lt_omega0
  have hu1c : u1 ≤ c := (lt_add_one u1).le.trans (right_le_opow _ one_lt_omega0)
  have hu1g : u1 ≤ g := hu1c.trans hcg
  have hωg : ω ≤ g := hωc.trans hcg
  have hgL1 : g < L1 := hgu2.trans hu2L1
  set lam := l + g with hlam
  set ν := l + g + ω ^ 2 with hνdef
  have hνa : ν = l + (g + ω ^ 2) := add_assoc _ _ _
  have hlamL1 : lam < L1 := hL1E.add_lt hlL1 hgL1
  have hω2L1 : ω ^ 2 < L1 := hω2le.trans_lt hgL1
  have hνL1 : ν < L1 := hL1E.add_lt hlamL1 hω2L1
  have hlamν : lam < ν := lt_add_of_pos_right lam ((vo_e2 ▸ opow_pos (2 : Ordinal.{0}) omega0_pos))
  have hllam : l < lam := lt_add_of_pos_right l (opow_pos c omega0_pos)
  have hlamR : IsRestartIdx lam := ⟨(hl0.trans hllam).ne', dvd_add hlR.2 hω2g⟩
  have hνR : IsRestartIdx ν := ⟨(hl0.trans (hllam.trans hlamν)).ne', dvd_add hlamR.2 dvd_rfl⟩
  -- the reach of `λ`
  have hcodeL : cdCode S lam = c := by
    rw [hlam, voCode_add k hωg hgu2]
    have he : cdExp g = c := by have := Sf.sfCdExp_any 0 c; rwa [zero_add] at this
    rw [he]; unfold cdOff; rw [if_neg (not_lt.2 hωc)]
  have hcρ : c ≤ upsilon lam := hcg.trans ((le_add_self).trans hm.le_apply)
  have hrL : cdR S lam = cdDelta lam + c := by
    rw [voR_low hlamR (hC lam hlamL1) (hcodeL ▸ hcρ), hcodeL]
  have hr' : cdR S (l + g) = upsilon (l + (g + ω + 1)) + ω ^ (u1 + 1) := by
    rw [← hlam, hrL]; unfold cdDelta; rw [hlam, add_assoc, add_assoc, add_assoc]
  -- the restart `ν`
  have hCR : CdRange S ν := by
    have h1 := hm (hllam.trans hlamν); rw [hlfix] at h1
    exact tkL_rng k ν hνR h1 (hbelow ν hνL1)
  have hcw : upsilon (l + Te.teW l) ≤ upsilon ν := by
    refine hm.monotone ?_
    have hW : Te.teW l ≤ u1 :=
      Te.teW_le hlE (hlL1.trans hL1O) hlu1 (upsPt_upsilon (hl0.trans_le le_self_add))
    calc l + Te.teW l ≤ l + g := (add_le_add_iff_left l).2 (hW.trans hu1g)
      _ ≤ ν := le_self_add
  have hlν : upsilon l < upsilon ν := hm (hllam.trans hlamν)
  have hcov : ¬ TkCov S (upsilon l) ν := by
    rintro ⟨R, hR, h1, h2, h3⟩
    have hlR' : l < R := hm.lt_iff_lt.1 h1
    have hRν : R < ν := hm.lt_iff_lt.1 h2
    obtain ⟨z, rfl⟩ := exists_add_of_le hlR'.le
    have hz0 : z ≠ 0 := by rintro rfl; rw [add_zero] at hlR'; exact lt_irrefl _ hlR'
    have hdz : ω ^ 2 ∣ z := (dvd_add_iff hlR.2).1 hR.1.2
    have hzg : z ≤ g := by
      by_contra hgz
      push Not at hgz
      obtain ⟨d, rfl⟩ := exists_add_of_le hgz.le
      have hd0 : d ≠ 0 := by rintro rfl; rw [add_zero] at hgz; exact lt_irrefl _ hgz
      have hdd : ω ^ 2 ∣ d := (dvd_add_iff hω2g).1 hdz
      have := le_of_dvd hd0 hdd
      rw [hνa] at hRν
      exact absurd ((add_lt_add_iff_left l).1 hRν) (not_lt.2 ((add_le_add_iff_left g).2 this))
    have hωz : ω ≤ z :=
      (calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
        _ ≤ ω ^ (2 : Ordinal.{0}) := opow_le_opow_right omega0_pos one_le_two
        _ = ω ^ 2 := vo_e2.symm).trans (le_of_dvd hz0 hdz)
    have hzu : z < u2 := hzg.trans_lt hgu2
    have hcode : cdCode S (l + z) ≤ z := by
      rw [voCode_add k hωz hzu]; exact (cdOff_le _).trans (Cp.cpExp_le hz0)
    have hlzL1 : l + z < L1 := hL1E.add_lt hlL1 (hzu.trans hu2L1)
    have hcodeρ : cdCode S (l + z) ≤ upsilon (l + z) := hcode.trans ((le_add_self).trans hm.le_apply)
    have hrR := voR_low hR.1 (hC _ hlzL1) hcodeρ
    have hE2 : InE (upsilon (l + z + ω + 2)) := upsPt_inE (upsPt_upsilon
      (lt_of_le_of_lt zero_le (lt_of_lt_of_le hlR' (le_self_add.trans le_self_add))))
    have hδ2 : cdDelta (l + z) < upsilon (l + z + ω + 2) := hm ((add_lt_add_iff_left _).2 one_lt_two)
    have hlt : cdR S (l + z) < upsilon (l + z + ω + 2) := by
      rw [hrR]; exact hE2.add_lt hδ2 ((hcodeρ.trans_lt (cdRho_lt_delta _)).trans hδ2)
    have hle : upsilon (l + z + ω + 2) ≤ upsilon ν := by
      refine hm.monotone ?_
      rw [hνa, add_assoc, add_assoc]
      refine (add_le_add_iff_left l).2 ?_
      calc z + (ω + 2) ≤ g + (ω + 2) := add_le_add_left hzg _
        _ ≤ g + ω ^ 2 := (add_le_add_iff_left g).2 vo_om2.le
    exact absurd (h3.trans (hlt.trans_le hle)) (lt_irrefl _)
  have hiso : TkIso S (upsilon l) ν := by
    refine ⟨upsilon lam, hm.monotone hllam.le, hm hlamν, fun ν' hν' h1 h2 => ?_⟩
    exfalso
    have hl1 : lam < ν' := hm.lt_iff_lt.1 h1
    have hl2 : ν' < ν := hm.lt_iff_lt.1 h2
    obtain ⟨d, rfl⟩ := exists_add_of_le hl1.le
    have hd0 : d ≠ 0 := by rintro rfl; rw [add_zero] at hl1; exact lt_irrefl _ hl1
    have hdd : ω ^ 2 ∣ d := (dvd_add_iff hlamR.2).1 hν'.1.2
    exact absurd ((add_lt_add_iff_left lam).1 hl2) (not_lt.2 (le_of_dvd hd0 hdd))
  have hτ : upsilon (l + 2) ≤ upsilon (l + (g + ω + 1)) :=
    hm.monotone ((add_le_add_iff_left l).2 (h2c.trans hcg |>.trans (le_self_add.trans le_self_add)))
  have hτ1 : upsilon (l + (g + ω + 1)) < Om1 := by
    refine (hbelow _ ?_).trans hL1O
    rw [← add_assoc, ← add_assoc]; exact hL1E.add_lt (hL1E.add_lt hlamL1 hωL1) (by exact_mod_cast hnatL1 1)
  have hc1 : upsilon (succ l) ≤ ω ^ (u1 + 1) := by rw [succ_eq_add_one]; exact hu1c
  refine ⟨ν, g, u1 + 1, hCR, hcw, hbelow ν hνL1, hlν, hcov, hiso, opow_pos c omega0_pos, hω2g,
    fun β hνβ => ?_, hr', opow_succ_mem u1, hc1, hcu2.trans_le hτ, hτ1, hl0⟩
  have hgβ' : g + ω ^ 2 < β := by
    have := hm.lt_iff_lt.1 hνβ; rw [hνa] at this; exact (add_lt_add_iff_left l).1 this
  exact ⟨(lt_add_of_pos_right g ((vo_e2 ▸ opow_pos (2 : Ordinal.{0}) omega0_pos))).trans hgβ',
    by rw [add_assoc]; exact ((add_le_add_iff_left g).2 vo_om2.le).trans hgβ'.le⟩

/-- **The decomposition road hypothesis is false at `L(k)`** (given `L(k+1) ≤ ν_C`): at the witness `ν` of `voWit`
every admissible `β` has the inner offset `g`, where none of `UbF3`, `UbForm`, `VlGdForm` holds. -/
theorem voNoGo (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) (w : Ordinal.{0}) :
    ¬ VlGdTyVis S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) w := by
  intro hvis
  obtain ⟨ν, g, e, hCR, hcw, hb, hlν, hcov, hiso, hg0, hgd, hβ, hr, hN, hc1, hcτ, hτ1, hl0⟩ := voWit k hν
  obtain ⟨β, hνβ, -, hG⟩ := hvis ν hCR hcw hb hlν hcov hiso
  obtain ⟨hgβ, hβ2⟩ := hβ β hνβ
  have hfail := voForms_fail (S := S) (β := β) hl0 hr hN hc1 hcτ hτ1 hβ2
  rcases hG.1 g hg0 hgβ hgd with h | h | h
  · exact hfail.1 h
  · exact hfail.2.1 h
  · exact hfail.2.2 h

/-- **The hypothesis `hn n` of `Vl.vlGdTyRoad` is false** (given `L(n+2) ≤ ν_C`). -/
theorem voNoGo_n (n : ℕ) (hν : Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ≤ nuC) :
    ¬ ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      VlGdTyVis S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
        (Nc.ncL S (n : Ordinal.{0})) := fun h =>
  voNoGo (n + 1) hν _ (h _ (Te.teRst_L (n + 1)) (Te.teUps_L (n + 1)).symm)

/-- **The hypothesis `h0` of `Vl.vlGdTyRoad` is false** (given `L(1) ≤ ν_C`). -/
theorem voNoGo_0 (hν : Nc.ncL S 1 ≤ nuC) :
    ¬ ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      VlGdTyVis S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))) (upsilon Rz.rzLam) := by
  intro h
  have h0 := voNoGo (S := S) 0 (by simpa using hν) (upsilon Rz.rzLam)
  have hl := Te.teRst_L (S := S) 0
  have he := (Te.teUps_L (S := S) 0).symm
  simp only [Nat.cast_zero, zero_add, Nat.cast_one] at h0 hl he
  exact h0 (h _ hl he)

/-- `L(k+1) ≤ ν_C` for every `k` under the road hypotheses `hU, hV, hVt, hL` (`Sh.shNu`). -/
theorem vo_L_le_nu (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (k : ℕ) :
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC :=
  ((Pp.ppL_lt_omega k).trans (Qq.qqL_lt_succ S)).le.trans (Sh.shNu hU hV hVt hL)

/-- **`Vl.vlGdTyRoad` is vacuous**: under its section hypotheses `hU, hV, hVt, hL` both `h0` and every `hn n` are
false. -/
theorem voNoGo_road (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) :
    (¬ ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      VlGdTyVis S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))) (upsilon Rz.rzLam)) ∧
    ∀ n : ℕ, ¬ ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      VlGdTyVis S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
        (Nc.ncL S (n : Ordinal.{0})) :=
  ⟨voNoGo_0 (by simpa using vo_L_le_nu hU hV hVt hL 0), fun n => voNoGo_n n (vo_L_le_nu hU hV hVt hL (n + 1))⟩

/-- **The same for `Uy.UyGdTyVis`** (`Vl.vlGdTyVis_of_uy`). -/
theorem voNoGo_uy (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) (w : Ordinal.{0}) :
    ¬ Uy.UyGdTyVis S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) w := fun h =>
  voNoGo k hν w (vlGdTyVis_of_uy (Te.teRst_L k) h)

/-- **The same for `Ur.UrGdTyVis`** (`Uy.uyGdTyVis_of_ur`). -/
theorem voNoGo_ur (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) (w : Ordinal.{0}) :
    ¬ Ur.UrGdTyVis S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) w := fun h =>
  voNoGo_uy k hν w (Uy.uyGdTyVis_of_ur (Te.teRst_L k) h)

/-- **The same for `Un.UnGdTyVis`** (`Uy.uyGdTyVis_of_un`). -/
theorem voNoGo_un (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) (w : Ordinal.{0}) :
    ¬ Un.UnGdTyVis S (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S (k : Ordinal.{0}) + Te.teW (Nc.ncL S (k : Ordinal.{0})))) w := fun h =>
  voNoGo_uy k hν w (Uy.uyGdTyVis_of_un (Te.teRst_L k) h)

end Googology.Trans.PoR.InaccPsi.R2.Vo
