import Googology.Trans.PoR.InaccPsi.R2.WmStep
import Googology.Trans.PoR.InaccPsi.R2.WnSucc

/-!
# WpLow: THE GATE-LOWERING EXTENSION ON THE (A2) ENTRIES `Wn.WnAt`

`Wm.WmExt` (the package relation that lowers by the pseudo-base gate), `Wm.wmExt_trans`, `Wm.wmSucc_ext` and
`Wm.wmPkL` are stated for arbitrary packages; only `Wm.wmLev_step` / `Wm.wmSucc_ext_lt` read the entries `Wh.WhAt`
of region (A1).  What differs on the (A2) entries `Wn.WnAt`: the reading `Gl.glR` / gate `Gl.glG` in place of
`Gf.rdc` / `Gf.gtc`, the bound `G = Γ_{Ω₁+1}` in place of `ε_{Ω₁+1}`, and the reading step `Wn.wn_glR_step` in place of
`Wh.wh_rdc_step`.

* `wpLev_step` (**the level and reading comparisons of two (A2) entries** at levels `ℓ'' < ℓ'`);
* `wpSucc_ext_lt` (**the successor entry extends, in the corrected sense `Wm.WmExt`, every (A2) entry that the entry
  at `ℓ'` extends**);
* `wpZ_le` (**the low field of an (A2) start is at most `Wn.wnZo`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wp

open Googology.Trans.PoR.InaccPsi.R2.Wh Googology.Trans.PoR.InaccPsi.R2.Ho
open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd
open Googology.Trans.PoR.InaccPsi.R2.Wm Googology.Trans.PoR.InaccPsi.R2.Wn Googology.Trans.PoR.InaccPsi.R2.Gk

/-- **The level and reading comparisons of two (A2) entries** at levels `ℓ'' < ℓ'` (`Wm.wmLev_step` with
`(rdc, ε_{Ω₁+1})` replaced by `(glR, G)`). -/
theorem wpLev_step {ℓ'' ℓ' : Ordinal.{0}} {K'' K' : HnPk} {V'' V' : HgVD} (hat'' : WnAt ℓ'' K'' V'')
    (hat' : WnAt ℓ' K' V') (hd'' : Om1 ∣ ℓ'') (hd' : Om1 ∣ ℓ') (hlt : ℓ'' < ℓ') (hG : ℓ' < gcG 0) :
    K''.Λ.L + Om1 ≤ K'.Λ.L ∧
    ∀ x, InE x → x < Om1 → K''.Λ.g < x → K'.Λ.g < x → K''.Λ.l x + x ≤ K'.Λ.l x := by
  refine ⟨by rw [hat''.1, hat'.1]; exact wh_lev_succ_le hd'' hd' hlt, fun x hx hx1 h1 h2 => ?_⟩
  rw [hat''.2.1 x hx hx1 h1, hat'.2.1 x hx hx1 h2]
  exact wn_glR_step hx hx1 hd'' hd' hlt hG (hat''.2.2.2.2.2.1 x hx hx1 h1) (hat'.2.2.2.2.2.1 x hx hx1 h2)

/-- **The successor (A2) entry extends, in the corrected sense, every entry that the entry at `ℓ'` extends**
(`Wm.wmSucc_ext_lt` on `Wn.WnAt`). -/
theorem wpSucc_ext_lt {ℓ'' ℓ' : Ordinal.{0}} {K'' K' : HnPk} {V'' V' : HgVD} (hat'' : WnAt ℓ'' K'' V'')
    (hat' : WnAt ℓ' K' V') (hd'' : Om1 ∣ ℓ'') (hd' : Om1 ∣ ℓ') (hlt : ℓ'' < ℓ') (hG : ℓ' < gcG 0)
    (hext : WmExt K'' K') : WmExt K'' K'.succ := by
  obtain ⟨hL, hl⟩ := wpLev_step hat'' hat' hd'' hd' hlt hG
  refine wmExt_trans hext (wmSucc_ext K') hL le_rfl (le_max_right _ _) (fun x hx hx1 h => ?_)
    (fun x _ _ _ => le_rfl)
  have h' : max K''.Λ.g K'.Λ.g < x := h
  exact hl x hx hx1 (max_lt_iff.1 h').1 (max_lt_iff.1 h').2

/-- **The low field of an (A2) start is at most `Wn.wnZo`.** -/
theorem wpZ_le {Λ : HnLv} {V : HgVD} (hsh : HnWShape (wnGW Λ) 0 V) {x : Ordinal.{0}} (hx : InE x)
    (hx1 : x < Om1) : V.Z x ≤ wnZo x := by
  rw [hsh.2.2.2.1 x hx hx1]
  split_ifs with h
  · have h1 : (1 : Ordinal.{0}) ≤ Λ.l x + 0 := by rw [add_zero]; exact WmLim.one_le_l Λ hx
    have h2 : Λ.l x + 0 < lgG x := by rw [add_zero]; exact Λ.l_lt x hx hx1
    refine (hb_evZ_lt_fix2 (wnZo_fix x) ?_).le
    show veblen (Λ.l x + 0) (lgG x + 1) < wnZo x
    rw [← hdNx_fixP (hjG_fix hx hx1 h1 h2)]
    exact wn_S_Zo hx hx1 h1 h2
  · have hg : ¬ (wnGW Λ).γR < x := fun h' => h (max_lt h' hx.pos)
    rw [(wnGW Λ).hnwZo_low hg]; exact le_rfl

end Googology.Trans.PoR.InaccPsi.R2.Wp
