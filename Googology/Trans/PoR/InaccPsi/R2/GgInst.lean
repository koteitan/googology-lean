import Googology.Trans.PoR.InaccPsi.R2.GgUni
import Googology.Trans.PoR.InaccPsi.R2.NnRoad
import Googology.Trans.PoR.InaccPsi.R2.LyEpR

/-!
# Terms for the codes below `ε_{Ω₁+1}` in `vzSys`, the layers `xtLL k` and `lyEB`; THEOREM UNI for them

`ggE` is the least `ε`-number above `Ω₁` (`ε_{Ω₁+1}`).  A code below `ggE` is built from constants and `Ω₁` by `+`
and `ω^·` (a `φ(a, b)` with `a ≠ 0` below `ggE` is a constant or `Ω₁`), and `Θ_y` sends `Ω₁` to `y` and commutes
with `+` and `ω^·` (`Gg.ggTh_Om1`, `Gg.ggTh_add`, `Gg.ggTh_opow`).  So:

* `ggPoly_vz` (**`vzSys` has terms for the codes below `ggE`**: constants, the base, sums and `ω^t` of `VzTm`);
* `ggPoly_next`, `ggPoly_lim`, `ggPoly_LL`, `ggPoly_iter`, `ggPoly_lyEB`: the terms pass to the next layer, the
  limit layer, every `xtLL k`, every `(xtLL k).iter n`, and `lyEB` (the terms `([], s)`);
* `ggVz`, `ggLL`, `ggLyE` (**THEOREM UNI for `VzOrec`, `O_{LL k}`, `O_E`**): `Θ_F(m_F) = O(F)` at every restart
  index `F = υ_F` with a name and `e(η_F) ≤ ggE`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Gg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt

variable {S : InaccSeq.{0}}

/-- **`vzSys` has terms for the codes below `ggE`.** -/
theorem ggPoly_vz : GgPoly vzSys ggE := by
  intro Z c hc
  induction hc with
  | @small x h =>
    intro _
    exact ⟨VzTm.cst x, fun y _ _ hZy =>
      ⟨lt_of_lt_of_le h hZy, by show x = ggTh y x; rw [ggTh_small (h.le.trans hZy)]⟩⟩
  | om =>
    intro _
    exact ⟨VzTm.bs, fun y hy hy1 _ => ⟨trivial, by show y = ggTh y (Om 1); rw [ggTh_Om1 hy hy1]⟩⟩
  | @add u v hu _ ihu ihv =>
    intro h
    obtain ⟨s1, hs1⟩ := ihu (lt_of_le_of_lt le_self_add h)
    obtain ⟨s2, hs2⟩ := ihv (lt_of_le_of_lt le_add_self h)
    refine ⟨VzTm.sm s1 s2, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
    obtain ⟨c2, v2⟩ := hs2 y hy hy1 hZy
    refine ⟨⟨c1, c2⟩, ?_⟩
    show vzSys.val s1 y + vzSys.val s2 y = _
    rw [v1, v2, ggTh_add hy (hu.mono hZy)]
  | @phi a b ha hb _ ihb =>
    intro h
    rcases eq_or_ne a 0 with rfl | ha0
    · obtain ⟨s, hs⟩ := ihb (lt_of_le_of_lt (right_le_veblen 0 b) h)
      refine ⟨VzTm.pw s, fun y hy hy1 hZy => ?_⟩
      obtain ⟨c1, v1⟩ := hs y hy hy1 hZy
      refine ⟨c1, ?_⟩
      show ω ^ vzSys.val s y = _
      rw [v1, veblen_zero_apply, ggTh_opow hy (hb.mono hZy)]
    · have hE := gg_veblen_eps (y := b) ha0
      have hle : veblen a b ≤ Om 1 := by
        by_contra hgt
        push Not at hgt
        exact absurd (ggE_le hE hgt) (not_le.2 h)
      have hmem : GgCl Z (veblen a b) := GgCl.phi ha hb
      rcases hle.lt_or_eq with hlt | heq
      · refine ⟨VzTm.cst (veblen a b), fun y hy _ hZy => ?_⟩
        have hvy : veblen a b < y := (hmem.mono hZy).lt_of_lt_Om1 hy hlt
        exact ⟨hvy, by show veblen a b = ggTh y (veblen a b); rw [ggTh_small hvy.le]⟩
      · refine ⟨VzTm.bs, fun y hy hy1 _ => ⟨trivial, ?_⟩⟩
        show y = ggTh y (veblen a b)
        rw [heq, ggTh_Om1 hy hy1]

/-- The terms pass to the next layer (`(0, s)`). -/
theorem ggPoly_next (L : XtLay) {E : Ordinal.{0}} (h : GgPoly L.sys E) : GgPoly L.xtNext.sys E := by
  intro Z c hc hcE
  obtain ⟨s, hs⟩ := h Z c hc hcE
  refine ⟨((0 : Ordinal.{0}), s), fun y hy hy1 hZy => ?_⟩
  obtain ⟨h1, h2⟩ := hs y hy hy1 hZy
  refine ⟨⟨hy.1, h1⟩, ?_⟩
  show L.sys.top y * 0 + L.sys.val s y = _
  rw [mul_zero, zero_add, h2]

/-- The terms pass to the limit layer (`⟨0, s⟩`). -/
theorem ggPoly_lim (L : XtLay) {E : Ordinal.{0}} (h : GgPoly L.sys E) : GgPoly L.xtLim.sys E := by
  intro Z c hc hcE
  obtain ⟨s, hs⟩ := h Z c hc hcE
  exact ⟨⟨0, s⟩, fun y hy hy1 hZy => hs y hy hy1 hZy⟩

theorem ggPoly_iter (L : XtLay) {E : Ordinal.{0}} (h : GgPoly L.sys E) : ∀ n, GgPoly (L.iter n).sys E
  | 0 => h
  | n + 1 => ggPoly_next (L.iter n) (ggPoly_iter L h n)

/-- **Every layer `xtLL k` has terms for the codes below `ggE`.** -/
theorem ggPoly_LL : ∀ k, GgPoly (xtLL k).sys ggE
  | 0 => ggPoly_vz
  | k + 1 => ggPoly_lim (xtLL k) (ggPoly_LL k)

/-- **`lyEB` has terms for the codes below `ggE`** (the terms `([], s)`). -/
theorem ggPoly_lyEB : GgPoly Ly.lyEB ggE := by
  intro Z c hc hcE
  obtain ⟨s, hs⟩ := ggPoly_vz Z c hc hcE
  refine ⟨(([] : List (Ly.LyTm × Ordinal.{0})), s), fun y hy hy1 hZy => ?_⟩
  obtain ⟨h1, h2⟩ := hs y hy hy1 hZy
  refine ⟨⟨List.Pairwise.nil, by simp [Ly.LeCo], h1⟩, ?_⟩
  show Ly.leVal vzLay ([], s) y = _
  rw [Ly.leVal_nil]; exact h2

/-! ## THEOREM UNI for `VzOrec`, the layers and `lyEB` -/

/-- **THEOREM UNI for `VzOrec`**: `Θ_F(m_F) = VzOrec(F)` at every named fixed point `F` with `e(η_F) ≤ ggE`. -/
theorem ggVz {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hX : upsilon F < Pv S ηx)
    (he : cdExp (cdEta S F) ≤ ggE) : cdTheta S F (cdCode S F) = VzOrec F := by
  rw [← xtVz_orec]; exact ggUniTh ggE_le_ggGam ggPoly_vz hF hfix hX he

/-- **THEOREM UNI for the layers `xtLL k`.** -/
theorem ggLL (k : ℕ) {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (he : cdExp (cdEta S F) ≤ ggE) :
    cdTheta S F (cdCode S F) = xtOrec (xtLL k).sys F :=
  ggUniTh ggE_le_ggGam (ggPoly_LL k) hF hfix hX he

/-- **THEOREM UNI for `lyEB`.** -/
theorem ggLyE {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hX : upsilon F < Pv S ηx)
    (he : cdExp (cdEta S F) ≤ ggE) : cdTheta S F (cdCode S F) = xtOrec Ly.lyEB F :=
  ggUniTh ggE_le_ggGam ggPoly_lyEB hF hfix hX he

end Googology.Trans.PoR.InaccPsi.R2.Gg
