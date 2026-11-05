import Googology.Trans.PoR.InaccPsi.R2.ZqY3
import Googology.Trans.PoR.InaccPsi.R2.SeLow

/-!
# The top over `Ω_ω`: `Zj.ZjTopG` from the wall and the atom move on the band `(ψ_{Ω₂}(Ω_ω + Y₃), P′)`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `θ = ψ_{Ω₂}(Ω_ω)`, `θ⁺ = Lj.ljThP`,
`K_Y = ψ_{Ω₂}(Ω_ω + Y₃)`, `P′ = ψ_{Ω₂}(Ω_ω·2)` (`Nc.ncPp`).

* `ZqAtHi S` (**the new leaf**: every atom `K_Y < s < P′` of a window restart moves once the codes below it
  move; the base-`Ω_ω` twin of the base-`0` wall statement `Ux.UxAtMove26`);
* `zqAtK_Pp` (**`ZqAtHi ⇒ Zj.ZjAtK S P′`**: below `K_Y` by `Zq.zqAtK_Y`, at `K_Y` by `Zq.zqY3_move`);
* `zqAtHi_of` (`Zj.ZjAtK S P′ ⇒ ZqAtHi`, so `ZqAtHi ⇔ ZjAtK S P′`);
* `zqCode_lt` (window codes are `< P′`: `Se.seCode_mid`);
* `zqTopG` (**`Wr.WrWallCF ∧ ZqAtHi ⇒ Zj.ZjTopG`**), `zqTopK` (**`⇒ Xs.XsTopK`**).

No new axiom.  New definition: the statement name `ZqAtHi`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Mv
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Zj

variable {S : InaccSeq.{0}}

/-- **The new leaf: the atom move on the band `ψ_{Ω₂}(Ω_ω + Y₃) < s < P′`** (window restarts, given the move of
the codes below `s`). -/
def ZqAtHi (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
    ∀ s ∈ ldAtR S l, S.psi (Om ω + ugY S) (Om (1 + 1)) < s → s < Nc.ncPp S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Nc.ncPp S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < Nc.ncPp S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

theorem zqKY_lt_Pp : S.psi (Om ω + ugY S) (Om (1 + 1)) < Nc.ncPp S :=
  psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left _).2 zqY_lt_OmW)
    (CSet.add_mem (zjOmW_own _) (Vq.vqY3_mem (Ry.ryOm3_lt.trans_le le_self_add)))

/-- **`ZqAtHi ⇒ Zj.ZjAtK S P′`.** -/
theorem zqAtK_Pp (h : ZqAtHi S) : ZjAtK S (Nc.ncPp S) := by
  intro n l l' hR h1 hr hl' hB s hs hθs hsK IH
  obtain ⟨hDK, hBK⟩ := zqB_Y (S := S) (n := n)
  rcases lt_trichotomy s (S.psi (Om ω + ugY S) (Om (1 + 1))) with hlt | heq | hgt
  · obtain ⟨a1, a2, a3, a4, a5⟩ := zqAtK_Y n l l' hR h1 hr hl' hB s hs hθs hlt (fun x hx hxs => by
      obtain ⟨b1, b2, -, b4, b5⟩ := IH x hx hxs
      refine ⟨b1, b2, ?_, b4, b5⟩
      have h := (mvB_lt_iff (k := n) b1 hDK).2 (hxs.trans hlt)
      rwa [hBK] at h)
    exact ⟨a1, a2, a3.trans zqKY_lt_Pp, a4, a5⟩
  · subst heq
    have hl := hR.1
    have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
    obtain ⟨hX, hX', hown, hown', -, -, -, -, -⟩ := Wr.wrWin hR h1 hr hl' hB
    obtain ⟨hAW, hAW'⟩ := zjWin_A hR h1 hr hl' hB
    refine ⟨hDK, by rw [hBK]; exact zqY3_atom hAW', by rw [hBK]; exact zqKY_lt_Pp, ?_, ?_⟩
    · rw [zqRead_Y3 hl hX hown hAW, add_assoc]
      exact (zqY3_bd hl hX hown hAW).2.trans hδr
    · rw [hBK]; exact (zqY3_move hR h1 hr hl' hB).symm
  · exact h n l l' hR h1 hr hl' hB s hs hgt hsK IH

/-- `Zj.ZjAtK S P′ ⇒ ZqAtHi` (so the leaf is exactly the atom move up to `P′`). -/
theorem zqAtHi_of (h : ZjAtK S (Nc.ncPp S)) : ZqAtHi S := by
  intro n l l' hR h1 hr hl' hB s hs hKs hsP IH
  have hθK : ConjT.th S < S.psi (Om ω + ugY S) (Om (1 + 1)) :=
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right _ (Uq.uqY_SC (S := S)).1) (zjOmW_own _)
  exact h n l l' hR h1 hr hl' hB s hs (hθK.trans hKs) hsP IH

theorem zqAtHi_iff : ZqAtHi S ↔ ZjAtK S (Nc.ncPp S) := ⟨zqAtK_Pp, zqAtHi_of⟩

/-- **Window codes are below `P′`.** -/
theorem zqCode_lt {n : ℕ} {l l' : Ordinal.{0}} (hW : R2Skel.SkEX.SkWin S n l l') : cdCode S l < Nc.ncPp S := by
  obtain ⟨hR, h1, hr, -, -, -⟩ := hW
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans ((cdR_ge S l).trans_lt hr)
  exact Se.seCode_mid hR.1.1 h1 h2

/-- **`Wr.WrWallCF ∧ ZqAtHi ⇒ Zj.ZjTopG`**: the reading move at every window code `m_λ ≥ F₂^ω`. -/
theorem zqTopG (hW : Wr.WrWallCF S) (h : ZqAtHi S) : ZjTopG S := by
  intro n l l' hW' hF
  have hc := zqCode_lt hW'
  obtain ⟨hR, h1, hr, hl', hB, -⟩ := hW'
  have hP : ljThP S ≤ cdCode S l := (zjThP_le_T.trans zjT_le_F2).trans hF
  exact zjMoveGen hW (SC_psi (InR_Om_succ 1) _) (zjThP_le_T.trans zjT_le_Pp) le_rfl (zqAtK_Pp h)
    n l l' hR h1 hr hl' hB hP hc

/-- **`Wr.WrWallCF ∧ ZqAtHi ⇒ Xs.XsTopK`.** -/
theorem zqTopK (hW : Wr.WrWallCF S) (h : ZqAtHi S) : Xs.XsTopK S := zjTopK_ofG hW (zqTopG hW h)

end Googology.Trans.PoR.InaccPsi.R2.Zq
