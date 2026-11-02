import Googology.Trans.PoR.InaccPsi.R2.YeGap

/-!
# The block leaf `Ye.YeGapBlk` holds

Notation as in `R2.YeGap`: a window `(n, λ, λ')`, an indecomposable cofinal far index `p`, `X = B_n p`, a gap point
`a` (`Ye.YeGapPt`: `a < X`, `B_n q ≤ a` for every `q < p`).

* `ykGapBlk` (**`Ye.YeGapBlk S` is a theorem**, no hypothesis): at a restart `p = υ_κ` the image `X = B_n υ_κ` is
  `υ_{κ'}` for a restart index `κ'` (`Sf.sfRstMove`); a gap `υ`-point `a` in the block `(υ_{botI μ j}, β]`,
  `β = υ_{μ+ω(j+1)+1}`, has `υ_μ ≤ υ_{botI μ j} < a < υ_{κ'}`, so `μ < κ'`; restart indices (and `0`) below `κ'`
  are `ω·ω` apart (`Ye.ye_rst_gap`), so `μ + ω(j+1) + 1 < μ + ω·ω ≤ κ'` and `β < υ_{κ'} = X`.
* `ykGapLh_of`: so under `L(ω+1) ≤ ν_C`, `Xw.XwGapLh S` follows from `Ye.YeGapEps S` and `Ye.YeGapRng S` alone.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- The image of a restart `p = υ_κ` of a gap configuration is `υ_{κ'}` for a restart index `κ'`. -/
theorem ykGap_img {n : ℕ} {l l' p a κ : Ordinal.{0}} (hP : Ye.YeGapPt S n l l' p a) (hκ : IsRestartIdx κ)
    (hpκ : p = upsilon κ) : ∃ κ', IsRestartIdx κ' ∧ Bc.bcB S n p = upsilon κ' := by
  obtain ⟨hW, hfar, hp, -, -, -, -, -⟩ := hP
  obtain ⟨hpC, -, -, hδp, -⟩ := Xw.xwWin hW hfar hp
  have h1p : Bc.bcC S n < p := hW.2.1.trans ((cdRho_lt_delta l).trans hδp)
  obtain ⟨κ', hκ', e⟩ := Sf.sfRstMove (S := S) n κ hκ (hpκ ▸ h1p.le) (hpκ ▸ hpC)
  exact ⟨κ', hκ', hpκ ▸ e⟩

/-- `μ ≤ botI μ j`. -/
theorem yk_le_botI (μ : Ordinal.{0}) (j : ℕ) : μ ≤ botI μ j := by
  obtain ⟨β₀, e, -, -⟩ := Ye.ye_botI_off μ j
  rw [e]; exact le_self_add

/-- **`Ye.YeGapBlk S` holds** (no hypothesis): the block top of a gap `υ`-point is below `B_n p`. -/
theorem ykGapBlk : Ye.YeGapBlk S := by
  intro n l l' p a μ κ j hP _ hκ hpκ hμ hb _
  obtain ⟨κ', hκ', hX⟩ := ykGap_img hP hκ hpκ
  have ha : a < upsilon κ' := hX ▸ hP.2.2.2.2.2.2.1
  have hμκ : μ < κ' := by
    have h1 : upsilon μ < upsilon κ' :=
      ((upsilon_normal.strictMono.monotone (yk_le_botI μ j)).trans_lt hb).trans ha
    exact upsilon_normal.strictMono.lt_iff_lt.1 h1
  have hgap := Ye.ye_rst_gap hμ hκ' hμκ
  obtain ⟨-, -, -, htop⟩ := Ye.ye_botI_off μ j
  rw [hX]
  exact upsilon_normal.strictMono (htop.trans_le hgap)

/-- **`Xw.XwGapLh` from the two remaining leaves** (under `L(ω+1) ≤ ν_C`). -/
theorem ykGapLh_of (hν : Nc.ncL S (ω + 1) ≤ nuC) (hE : Ye.YeGapEps S) (hR : Ye.YeGapRng S) :
    Xw.XwGapLh S :=
  Ye.yeGapLh_of hν hE hR ykGapBlk

end Googology.Trans.PoR.InaccPsi.R2.Yk
