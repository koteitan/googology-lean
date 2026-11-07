import Googology.Trans.PoR.InaccPsi.R2.ZbLoc
import Googology.Trans.PoR.InaccPsi.R2.TzDL
import Googology.Trans.PoR.InaccPsi.R2.TzB
import Googology.Trans.PoR.InaccPsi.R2.TwHull

/-!
# ZbTl: THE ATOM SYSTEM OF ALL CODES BELOW `X` (ATOMS: THE VALUES OF EVERY `F_β` ABOVE `Ω₁`)

The codes of `Tl.TlCl Z` (from the ordinals below `Z`, `Ω₁`, `+`, `φ` and the atoms `F_β(y) > Ω₁` with `β`, `y`
codes) below `X = Tl.tlX` form an atom system `zbTl : Zb.ZbAS`: the atoms over `Z` are the strongly critical codes
`Ω₁ < s < X` of `TlCl Z`; the hull lemma is `Tz.tz_diglev`, hull membership `Tw.tw_mem_CSet` with `Tz.tz_args_W`.
So the frontier lemma `Zb.zbB1_eq` and `Zb.zbUV` hold with every atom of kind `β` (`B_Γ` and the fixed points of
`Γ` included).

* `zbTlAt`, `zbTl_supp` (**support of codes below every strongly critical `Z`**), `zbTl_gx` / `zbTl_of_gx`
  (**`GxCl Z (zbTlAt Z) x ⇔ TlCl Z x` below `X`**), `zbTl` (**THE ATOM SYSTEM BELOW `X`**), `zbTl_V`, `zbTl_BG`
  (`B_Γ` is an atom over every `Z`).

No new axiom.  New definitions: `zbTlAt`, `zbTl`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Tz
  Googology.Trans.PoR.InaccPsi.R2.Tw Googology.Trans.PoR.InaccPsi.R2.Tf

/-- **The atoms over `Z`**: the strongly critical codes `Ω₁ < s < X` of `TlCl Z`. -/
def zbTlAt (Z : Ordinal.{0}) : Set Ordinal.{0} := {s | SC s ∧ Om 1 < s ∧ s < tlX ∧ TlCl Z s}

/-- **A code over a strongly critical `Z` is a code over some `Z' < Z`.** -/
theorem zbTl_supp {Z : Ordinal.{0}} (hZ : SC Z) {x : Ordinal.{0}} (hx : TlCl Z x) : ∃ Z' < Z, TlCl Z' x := by
  have h1 := gg_one_lt_of_SC hZ
  induction hx with
  | @small x h => exact ⟨x + 1, hZ.isPrincipal h h1, TlCl.small (lt_add_one x)⟩
  | om => exact ⟨0, hZ.1, TlCl.om⟩
  | add _ _ ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', TlCl.add (g1.mono (le_max_left _ _)) (g2.mono (le_max_right _ _))⟩
  | phi _ _ ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', TlCl.phi (g1.mono (le_max_left _ _)) (g2.mono (le_max_right _ _))⟩
  | atom _ _ hlt ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', TlCl.atom (g1.mono (le_max_left _ _)) (g2.mono (le_max_right _ _)) hlt⟩

/-- **A code of `TlCl Z` below `X` is a code over the atoms `zbTlAt Z`.** -/
theorem zbTl_gx {Z : Ordinal.{0}} {x : Ordinal.{0}} (hx : TlCl Z x) : x < tlX → GxCl Z (zbTlAt Z) x := by
  induction hx with
  | small h => exact fun _ => GxCl.small h
  | om => intro _; rw [Br.Om1_eq]; exact GxCl.om
  | @add x y _ _ ihx ihy =>
    exact fun h => GxCl.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => GxCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))
  | @atom β y hβ hy hlt _ _ =>
    intro h
    exact GxCl.atom ⟨rhF_SC β y, by rw [← Br.Om1_eq]; exact hlt, h, TlCl.atom hβ hy hlt⟩

/-- **A code over the atoms `zbTlAt Z` is a code of `TlCl Z`.** -/
theorem zbTl_of_gx {Z : Ordinal.{0}} {x : Ordinal.{0}} (hx : GxCl Z (zbTlAt Z) x) : TlCl Z x := by
  induction hx with
  | small h => exact TlCl.small h
  | om => rw [← Br.Om1_eq]; exact TlCl.om
  | atom hs => exact hs.2.2.2
  | add _ _ ihx ihy => exact TlCl.add ihx ihy
  | phi _ _ ihx ihy => exact TlCl.phi ihx ihy

/-- **THE ATOM SYSTEM BELOW `X`**: atoms the strongly critical codes `Ω₁ < s < X`, bound `X`. -/
noncomputable def zbTl : ZbAS where
  At := zbTlAt
  V := tlX
  V_SC := tlX_SC
  V_lt := tlX_lt_Om2
  Om1_lt_V := by rw [← Br.Om1_eq]; exact tlX_gt
  gxAt := fun _ s hs => ⟨hs.1, hs.2.1⟩
  mono := fun _ _ h _ hs => ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.mono h⟩
  lt_V := fun _ _ hs => hs.2.2.1
  supp := fun _ s hZ hs => by
    obtain ⟨Z', hZ', h'⟩ := zbTl_supp hZ hs.2.2.2
    exact ⟨Z', hZ', hs.1, hs.2.1, hs.2.2.1, h'⟩

theorem zbTl_ok (S : InaccSeq.{0}) : zbTl.Ok S where
  mem := fun a b Z s ha hb hb1 hZb _ hs => by
    have hb1' : b ≤ Om1 := by rw [Br.Om1_eq]; exact hb1
    have hW : Le.leWe (Om (1 + 1)) ≤ a := tz_W_lt_Omw.le.trans (le_self_add.trans ha)
    exact (tw_mem_CSet (S := S) hb hb1' le_rfl s (hs.2.2.2.mono hZb) (tz_args_W hW hs.2.2.1)).1
  hull := fun a Z hZ hZ1 hkey x hx hxV => by
    have hcoll : ∀ e, e < a → e ∈ S.CSet a Z → Ri.RiDg Z e → TzLev Z e → S.psi e (Om 1) < Z :=
      fun e hea heC _ _ => hkey _ (CSet.psi_mem hea Low.InR_Om_one (CSet.Om_mem (CSet.one_mem _ _)) heC)
        (psi_lt Low.InR_Om_one _)
    obtain ⟨-, -, hT, -⟩ := tz_diglev (S := S) hZ hZ1 hcoll x hx
    exact zbTl_gx (hT hxV) hxV

instance (S : InaccSeq.{0}) : Fact (zbTl.Ok S) := ⟨zbTl_ok S⟩

theorem zbTl_V : zbTl.V = tlX := rfl

theorem zbTl_At (Z : Ordinal.{0}) : zbTl.At Z = zbTlAt Z := rfl

/-- **`GxCl Z (zbTl.At Z) x ⇔ TlCl Z x` below `X`.** -/
theorem zbTl_cl_iff {Z x : Ordinal.{0}} (hx : x < tlX) : GxCl Z (zbTl.At Z) x ↔ TlCl Z x :=
  ⟨zbTl_of_gx, fun h => zbTl_gx h hx⟩

end Googology.Trans.PoR.InaccPsi.R2.Zb
