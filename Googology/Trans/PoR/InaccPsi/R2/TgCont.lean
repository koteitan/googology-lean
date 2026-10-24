import Googology.Trans.PoR.InaccPsi.R2.TdDer
import Googology.Trans.PoR.InaccPsi.R2.LwFix

/-!
# Continuity of `T` at limits, the code gap below a level, and the own condition of every smaller level

`W^E = Ω₂^E` (`Le.leWe`), `T_E(β, X₀) = ψ_{Ω₂}(β + W^{X₀ + W^E})`, codes = `Le.LeCl Ω₂ Q` (`Q` strongly critical),
`φ = veblen`, `SjDesc Q e` the descent property of an evaluation `e` (`Sj.SjDesc`).

* `tgPsi_contN` (**CONTINUITY**: for `κ ∈ R`, a normal `F` and a limit `E`, every `x < ψ_κ(F E)` is below
  `ψ_κ(F E')` for some `E' < E`; from `Lw.lw_psi_limit`, i.e. from the definition of `ψ` by the closure `Cl`),
  `tgArg_normal`, `tgT_cont` (**`E ↦ T_{e(E)}` is continuous at limits** for a normal `e`), `tgT_iSup`
  (`T_E = sup_{E' < E} T_{E'}` at a limit `E`);
* `tgLev_tail` (**THE TAIL AT A LIMIT LEVEL**: `x < T_{e(φ(c, z+1))}`, `c` a limit, gives `c₀ < c` with
  `x < T_{e(φ(c', φ(c, z) + 1))}` for every `c' ≥ c₀`);
* `tgGap` (**THE CODE GAP BELOW A LEVEL**: for `Q ≤ η < Ω₂`, `a < Ω₂`, `Ω₂ < φ(η, y)`, `U < φ(η, y)`, no code over
  `Q` lies in `[φ(η, y), φ(a, U)]`), `tgGapF` (**THE CODE GAP UP TO `φ(Ω₂, 1)`**: for `Q ≤ η` and `Ω₂ < φ(η, y)`,
  no code over `Q` lies in `[φ(η, y), φ(Ω₂, 1))`; uses `φ(Ω₂, 0) = Ω₂`);
* `tgCode_in` (the closure condition of `E` and the descent of `e` give a code over `T_{e(u)}` in `[u, V)` when
  `e(u) ≤ E < e(V)`, by `Sj.sjCode`);
* `tgLevOwn` (**THE OWN CONDITION OF A LEVEL**: with the closure condition of `E`, `e(φ(η, y)) ≤ E < e(φ(a, U))`,
  `η, a < Ω₂`, `Ω₂ ≤ y < φ(η, y)`, `U < φ(η, y)`: `η < T_{e(φ(η, y))}`), `tgLevOwn_ge` (the same at every node
  `φ(η, w)`, `w ≥ y`: so **every smaller level `c′ ∈ [ψ₂(0), Ω₂)` is below `T` at its node**), `tgLevOwnF`
  (**the same at every node `φ(η, y) > Ω₂` with a top `V ≤ φ(Ω₂, 1)`**, no non-fixedness); no continuity is
  needed for these, only the gaps.

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td

variable {S : InaccSeq.{0}}

/-! ## Continuity -/

/-- **CONTINUITY OF `ψ_κ` ALONG A NORMAL MAP**: for `κ ∈ R`, `F` normal and `E` a limit, every `x < ψ_κ(F E)` is
below `ψ_κ(F E')` for some `E' < E`. -/
theorem tgPsi_contN {κ : Ordinal.{0}} (hκ : S.InR κ) {F : Ordinal.{0} → Ordinal.{0}} (hF : Order.IsNormal F)
    {E x : Ordinal.{0}} (hE : IsSuccLimit E) (hx : x < S.psi (F E) κ) : ∃ E', E' < E ∧ x < S.psi (F E') κ := by
  have hFE : IsSuccLimit (F E) := hF.map_isSuccLimit hE
  rw [Lw.lw_psi_limit S hκ hFE] at hx
  have hbdd : BddAbove (range fun e : Iio (F E) => S.psi e.1 κ) :=
    ⟨κ, by rintro _ ⟨e, rfl⟩; exact (psi_lt hκ _).le⟩
  haveI : Nonempty (Iio (F E)) := ⟨⟨0, hFE.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff hbdd).1 hx
  obtain ⟨E', hE', hlt⟩ := (hF.lt_iff_exists_lt hE).1 e.2
  exact ⟨E', hE', he.trans_le (psi_mono (S := S) hκ hlt.le).1⟩

/-- The argument map `E ↦ β + W^{X₀ + W^{e(E)}}` is normal for a normal `e`. -/
theorem tgArg_normal (b X0 : Ordinal.{0}) {e : Ordinal.{0} → Ordinal.{0}} (he : Order.IsNormal e) :
    Order.IsNormal (fun E => b + leWe (X0 + leWe (e E))) := by
  have hW : Order.IsNormal leWe := (isNormal_opow one_lt_omega0).comp (isNormal_mul_right ldOm2_SC.1)
  exact (isNormal_add_right b).comp (hW.comp ((isNormal_add_right X0).comp (hW.comp he)))

/-- **`E ↦ T_{e(E)}` IS CONTINUOUS AT LIMITS** (`e` normal). -/
theorem tgT_cont {b X0 E x : Ordinal.{0}} {e : Ordinal.{0} → Ordinal.{0}} (he : Order.IsNormal e)
    (hE : IsSuccLimit E) (hx : x < S.psi (b + leWe (X0 + leWe (e E))) (Om (1 + 1))) :
    ∃ E', E' < E ∧ x < S.psi (b + leWe (X0 + leWe (e E'))) (Om (1 + 1)) :=
  tgPsi_contN (InR_Om_succ 1) (tgArg_normal b X0 he) hE hx

/-- **`T_E = sup_{E' < E} T_{E'}`** at a limit `E`. -/
theorem tgT_iSup {b X0 E : Ordinal.{0}} (hE : IsSuccLimit E) :
    S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1)) =
      ⨆ E' : Iio E, S.psi (b + leWe (X0 + leWe E'.1)) (Om (1 + 1)) := by
  have hbdd : BddAbove (range fun E' : Iio E => S.psi (b + leWe (X0 + leWe E'.1)) (Om (1 + 1))) :=
    ⟨Om (1 + 1), by rintro _ ⟨e, rfl⟩; exact (psi_lt (InR_Om_succ 1) _).le⟩
  haveI : Nonempty (Iio E) := ⟨⟨0, hE.bot_lt⟩⟩
  have hmono : ∀ {x y : Ordinal.{0}}, x ≤ y → S.psi (b + leWe (X0 + leWe x)) (Om (1 + 1)) ≤
      S.psi (b + leWe (X0 + leWe y)) (Om (1 + 1)) := fun h =>
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono
      ((add_le_add_iff_left X0).2 (leWe_mono h))))).1
  refine le_antisymm (not_lt.1 fun h => ?_) (ciSup_le fun E' => hmono E'.2.le)
  obtain ⟨E', hE', hlt⟩ := tgT_cont (e := fun y => y) Order.IsNormal.id hE h
  exact absurd (le_ciSup hbdd ⟨E', hE'⟩) (not_le.2 hlt)

/-- **THE TAIL AT A LIMIT LEVEL**: `x < T_{e(φ(c, z+1))}` with `c` a limit gives `c₀ < c` such that
`x < T_{e(φ(c', φ(c, z) + 1))}` for every `c' ≥ c₀`. -/
theorem tgLev_tail {b X0 c z x : Ordinal.{0}} {e : Ordinal.{0} → Ordinal.{0}} (he : Order.IsNormal e)
    (hc : IsSuccLimit c) (hx : x < S.psi (b + leWe (X0 + leWe (e (veblen c (z + 1))))) (Om (1 + 1))) :
    ∃ c0, c0 < c ∧ ∀ c', c0 ≤ c' →
      x < S.psi (b + leWe (X0 + leWe (e (veblen c' (veblen c z + 1))))) (Om (1 + 1)) := by
  have hL : IsSuccLimit (veblen c (z + 1)) := taVeb_lim hc.ne_bot
  obtain ⟨E', hE', hxE'⟩ := tgT_cont he hL hx
  obtain ⟨c0, hc0, hE'c0⟩ := taVeb_lim_cof hc hE'
  refine ⟨c0, hc0, fun c' hc' => hxE'.trans_le ?_⟩
  exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono ((add_le_add_iff_left X0).2
    (leWe_mono (he.monotone (hE'c0.le.trans (veblen_left_monotone _ hc')))))))).1

/-! ## The code gap below a level -/

/-- **THE CODE GAP BELOW A LEVEL**: for `Q ≤ η < Ω₂`, `a < Ω₂`, `Ω₂ < φ(η, y)` and `U < φ(η, y)`, every code
over `Q` is below `φ(η, y)` or above `φ(a, U)`. -/
theorem tgGap {Q η a y U : Ordinal.{0}} (hQ : SC Q) (hQη : Q ≤ η) (hηW : η < Om (1 + 1))
    (haW : a < Om (1 + 1)) (hΩ : Om (1 + 1) < veblen η y) (hU : U < veblen η y) :
    ∀ w, LeCl (Om (1 + 1)) Q w → w < veblen η y ∨ veblen a U < w := by
  intro w hw
  induction hw with
  | small h => exact Or.inl (h.trans_le (hQη.trans (left_le_veblen η y)))
  | om => exact Or.inl hΩ
  | @add x z _ _ ihx ihz =>
    rcases ihx with hx | hx
    · rcases ihz with hz | hz
      · exact Or.inl (Ph.ph_veblen_prin η y hx hz)
      · exact Or.inr (hz.trans_le le_add_self)
    · exact Or.inr (hx.trans_le le_self_add)
  | @phi p q hp _ ihp ihq =>
    rcases ihq with hq' | hq'
    · rcases ihp with _ | hp'
      · rcases lt_or_ge p η with hpη | hηp
        · left
          calc veblen p q < veblen p (veblen η y) := (veblen_lt_veblen_iff_right).2 hq'
            _ = veblen η y := veblen_veblen_of_lt hpη y
        · have hpW : Om (1 + 1) ≤ p := by
            by_contra h
            push Not at h
            exact absurd (hQη.trans hηp) (not_le.2 (LeCl.lt_of_lt hQ hp h))
          have hfa : veblen a (veblen p q) = veblen p q := veblen_veblen_of_lt (haW.trans_le hpW) q
          have hfη : veblen η (veblen p q) = veblen p q := veblen_veblen_of_lt (hηW.trans_le hpW) q
          rcases lt_or_ge (veblen p q) y with h1 | h1
          · exact Or.inl (h1.trans_le (right_le_veblen η y))
          · right
            have hUp : U < veblen p q :=
              hU.trans_le (by rw [← hfη]; exact (veblen_le_veblen_iff_right).2 h1)
            calc veblen a U < veblen a (veblen p q) := (veblen_lt_veblen_iff_right).2 hUp
              _ = veblen p q := hfa
      · exact Or.inr (hp'.trans_le (left_le_veblen p q))
    · exact Or.inr (hq'.trans_le (right_le_veblen p q))

/-- **THE CODE GAP UP TO `φ(Ω₂, 1)`**: for `Q ≤ η` and `Ω₂ < φ(η, y)`, every code over `Q` is below `φ(η, y)`
or at least `φ(Ω₂, 1)` (`φ(Ω₂, 0) = Ω₂`: the only code `≥ Ω₂` built with a level `≥ Ω₂` below `φ(Ω₂, 1)` is
`Ω₂` itself). -/
theorem tgGapF {Q η y : Ordinal.{0}} (hQ : SC Q) (hQη : Q ≤ η) (hΩ : Om (1 + 1) < veblen η y) :
    ∀ w, LeCl (Om (1 + 1)) Q w → w < veblen η y ∨ veblen (Om (1 + 1)) 1 ≤ w := by
  intro w hw
  induction hw with
  | small h => exact Or.inl (h.trans_le (hQη.trans (left_le_veblen η y)))
  | om => exact Or.inl hΩ
  | @add x z _ _ ihx ihz =>
    rcases ihx with hx | hx
    · rcases ihz with hz | hz
      · exact Or.inl (Ph.ph_veblen_prin η y hx hz)
      · exact Or.inr (hz.trans le_add_self)
    · exact Or.inr (hx.trans le_self_add)
  | @phi p q hp _ ihp ihq =>
    rcases ihq with hq' | hq'
    · rcases ihp with _ | hp'
      · rcases lt_or_ge p η with hpη | hηp
        · left
          calc veblen p q < veblen p (veblen η y) := (veblen_lt_veblen_iff_right).2 hq'
            _ = veblen η y := veblen_veblen_of_lt hpη y
        · have hpW : Om (1 + 1) ≤ p := by
            by_contra h
            push Not at h
            exact absurd (hQη.trans hηp) (not_le.2 (LeCl.lt_of_lt hQ hp h))
          rcases eq_or_ne q 0 with rfl | hq0
          · rcases eq_or_lt_of_le hpW with hpe | hpl
            · exact Or.inl (by rw [← hpe, ldOm2_SC.veblen_zero]; exact hΩ)
            · right
              have hfix : veblen (Om (1 + 1)) (veblen p 0) = veblen p 0 := veblen_veblen_of_lt hpl 0
              rw [← hfix]
              exact (veblen_le_veblen_iff_right).2 (Order.one_le_iff_pos.2 veblen_pos)
          · right
            exact ((veblen_le_veblen_iff_right).2 (Order.one_le_iff_ne_zero.2 hq0)).trans
              (veblen_left_monotone q hpW)
      · exact Or.inr (hp'.trans (left_le_veblen p q))
    · exact Or.inr (hq'.trans (right_le_veblen p q))

/-! ## The own condition of a level from the closure condition -/

section Own

variable {β X0 E : Ordinal.{0}}
  (hβd : leWe (X0 + leWe E) ∣ β)
  (hβown : ∀ d, d ≤ leWe (X0 + leWe E) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
  (hX0G3 : X0 + leWe E < S.psi 0 (Om (1 + 1 + 1)))
  (hEcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E)

include hβd hβown hX0cl hX0G3 hEcl

/-- **A code over `T_{e(u)}` in `[u, V)`** when `e(u) ≤ E < e(V)` (`Sj.sjCode` and the descent of `e`). -/
theorem tgCode_in {e : Ordinal.{0} → Ordinal.{0}} (he : Monotone e)
    (hD : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe (e 0))) (Om (1 + 1)) ≤ Q → SjDesc Q e)
    {u V : Ordinal.{0}} (hlo : e u ≤ E) (hhi : E < e V) :
    ∃ w, LeCl (Om (1 + 1)) (S.psi (β + leWe (X0 + leWe (e u))) (Om (1 + 1))) w ∧ u ≤ w ∧ w < V := by
  obtain ⟨z, hz1, hz2, hz⟩ := sjCode hβd hβown hX0cl hX0G3 hEcl hlo
  have hQ : SC (S.psi (β + leWe (X0 + leWe (e u))) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
  exact hD _ hQ (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono
    ((add_le_add_iff_left X0).2 (leWe_mono (he zero_le)))))).1 u V z hz hz1 (hz2.trans_lt hhi)

/-- **THE OWN CONDITION OF A LEVEL**: with the closure condition of `E` and `e(φ(η, y)) ≤ E < e(φ(a, U))`
(`η, a < Ω₂`, `Ω₂ ≤ y < φ(η, y)`, `U < φ(η, y)`), the level `η` is below `T_{e(φ(η, y))}`. -/
theorem tgLevOwn {e : Ordinal.{0} → Ordinal.{0}} (he : Monotone e)
    (hD : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe (e 0))) (Om (1 + 1)) ≤ Q → SjDesc Q e)
    {η a y U : Ordinal.{0}} (hηW : η < Om (1 + 1)) (haW : a < Om (1 + 1)) (hΩy : Om (1 + 1) ≤ y)
    (hy : y < veblen η y) (hU : U < veblen η y) (hlo : e (veblen η y) ≤ E) (hhi : E < e (veblen a U)) :
    η < S.psi (β + leWe (X0 + leWe (e (veblen η y)))) (Om (1 + 1)) := by
  by_contra hc
  push Not at hc
  obtain ⟨w, hw, hw1, hw2⟩ := tgCode_in hβd hβown hX0cl hX0G3 hEcl he hD hlo hhi
  rcases tgGap (SC_psi (InR_Om_succ 1) _) hc hηW haW (hΩy.trans_lt hy) hU w hw with h | h
  · exact absurd hw1 (not_le.2 h)
  · exact absurd hw2 (not_lt.2 h.le)

/-- **EVERY SMALLER LEVEL IS BELOW `T` AT ITS NODE**: under the hypotheses of `tgLevOwn`, `η < T_{e(φ(η, w))}` for
every `w ≥ y` (in particular for the members `φ(c', φ(c, z) + 1)` of a limit level `c`). -/
theorem tgLevOwn_ge {e : Ordinal.{0} → Ordinal.{0}} (he : Monotone e)
    (hD : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe (e 0))) (Om (1 + 1)) ≤ Q → SjDesc Q e)
    {η a y U w : Ordinal.{0}} (hηW : η < Om (1 + 1)) (haW : a < Om (1 + 1)) (hΩy : Om (1 + 1) ≤ y)
    (hy : y < veblen η y) (hU : U < veblen η y) (hlo : e (veblen η y) ≤ E) (hhi : E < e (veblen a U))
    (hyw : y ≤ w) : η < S.psi (β + leWe (X0 + leWe (e (veblen η w)))) (Om (1 + 1)) :=
  (tgLevOwn hβd hβown hX0cl hX0G3 hEcl he hD hηW haW hΩy hy hU hlo hhi).trans_le
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono ((add_le_add_iff_left X0).2
      (leWe_mono (he ((veblen_le_veblen_iff_right).2 hyw))))))).1

/-- **THE OWN CONDITION OF A LEVEL AT EVERY NODE BELOW `φ(Ω₂, 1)`**: with the closure condition of `E` and
`e(φ(η, y)) ≤ E < e(V)`, `Ω₂ < φ(η, y)`, `V ≤ φ(Ω₂, 1)`: `η < T_{e(φ(η, y))}` (no non-fixedness, no bound on `η`). -/
theorem tgLevOwnF {e : Ordinal.{0} → Ordinal.{0}} (he : Monotone e)
    (hD : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe (e 0))) (Om (1 + 1)) ≤ Q → SjDesc Q e)
    {η y V : Ordinal.{0}} (hΩ : Om (1 + 1) < veblen η y) (hV : V ≤ veblen (Om (1 + 1)) 1)
    (hlo : e (veblen η y) ≤ E) (hhi : E < e V) :
    η < S.psi (β + leWe (X0 + leWe (e (veblen η y)))) (Om (1 + 1)) := by
  by_contra hc
  push Not at hc
  obtain ⟨w, hw, hw1, hw2⟩ := tgCode_in hβd hβown hX0cl hX0G3 hEcl he hD hlo hhi
  rcases tgGapF (SC_psi (InR_Om_succ 1) _) hc hΩ w hw with h | h
  · exact absurd hw1 (not_le.2 h)
  · exact absurd (hw2.trans_le hV) (not_lt.2 h)

end Own

end Googology.Trans.PoR.InaccPsi.R2.Tg
