import Googology.Trans.PoR.InaccPsi.R2.VqSucc
import Googology.Trans.PoR.InaccPsi.R2.VqY3

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Ld

/-- A top law whose image of the outer `W^X` term may depend on the visible base β.
The constant-image version is `Rv.RvTop`; `leOe` writes the corresponding Ω₁-power. -/
def VtTopDyn (S : InaccSeq.{0}) (l b X : Ordinal.{0}) (Xh : Ordinal.{0} → Ordinal.{0})
    (e : Ordinal.{0}) : Prop :=
  ∀ β Â, RoBaseE S l X e β → b ≤ β →
    Â ∈ S.CSet Â (S.psi Â (Om 1)) →
    gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1) →
    gxTh (upsilon l) (ldAtR S l) (leTe S (X + e) β) =
      S.psi (Â + leOe (Xh β + gxTh (upsilon l) (ldAtR S l) e)) (Om 1)

/-- Every existing `RvTop` law is the constant-image special case of `VtTopDyn`. -/
theorem vtTopDyn_const {S : InaccSeq.{0}} {l b X Xh e : Ordinal.{0}}
    (h : Rv.RvTop S l b X Xh e) :
    VtTopDyn S l b X (fun _ => Xh) e := by
  intro β Â hβ hb hÂ hbase
  exact h β Â hβ hb hÂ hbase

/-- The established high-base Y₃ top rule is an instance with constant image Ω₂². -/
theorem vtTopY3_const {S : InaccSeq.{0}} {l ηx A b : Ordinal.{0}}
    (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (hb : Om (1 + 1 + 1) ≤ b) :
    VtTopDyn S l b (Ug.ugY S) (fun _ => S.psi (Om (1 + 1)) (Om (1 + 1))) 0 :=
  vtTopDyn_const (Vq.vqTopY3 hl hX hA hρ hb)

/-- The successor rule for the dynamic-top interface in its constant-image case.
The rule is the existing `Vq.vqTopSucc`; this wrapper records precisely the
specialization `Xh β = Xh`. -/
theorem vtTopDyn_succ_const {S : InaccSeq.{0}} {l A b X Xh e ηx : Ordinal.{0}}
    (hs : Vq.VqSh S l A b X Xh) (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hAo : A ∈ S.CSet A (S.psi A (Om 1))) (hρo : S.psi A (Om 1) = upsilon l)
    (hec : GxCl (upsilon l) (ldAtR S l) e) (hT : Rv.RvTop S l b X Xh e) :
    VtTopDyn S l b X (fun _ => Xh) (e + 1) :=
  vtTopDyn_const (Vq.vqTopSucc hs hl hX hAo hρo hec hT)

/-- A successor top remains valid for a base-dependent image if that image is
constant on the bases reached from the shift's starting base. Its values below
that base are unconstrained. -/
theorem vtTopDyn_succ_of_stable {S : InaccSeq.{0}}
    {l A b X Xh e ηx : Ordinal.{0}} (hs : Vq.VqSh S l A b X Xh)
    (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hAo : A ∈ S.CSet A (S.psi A (Om 1))) (hρo : S.psi A (Om 1) = upsilon l)
    (hec : GxCl (upsilon l) (ldAtR S l) e) (hT : Rv.RvTop S l b X Xh e)
    (Xhd : Ordinal.{0} → Ordinal.{0})
    (hstable : ∀ β, b ≤ β → Xhd β = Xh) :
    VtTopDyn S l b X Xhd (e + 1) := by
  intro β Â hb hbβ hÂ hbase
  rw [hstable β hbβ]
  exact Vq.vqTopSucc hs hl hX hAo hρo hec hT β Â hb hbβ hÂ hbase

/-- Any existing top law yields a dynamic-image law when the image agrees
with its constant value on all bases in the law's range. -/
theorem vtTopDyn_of_stable {S : InaccSeq.{0}} {l b X Xh e : Ordinal.{0}}
    (hT : Rv.RvTop S l b X Xh e) (Xhd : Ordinal.{0} → Ordinal.{0})
    (hstable : ∀ β, b ≤ β → Xhd β = Xh) : VtTopDyn S l b X Xhd e := by
  intro β Â hb hbβ hÂ hbase
  rw [hstable β hbβ]
  exact hT β Â hb hbβ hÂ hbase

/-- For the `(Y₃,Y₂)` shift, a possibly different image below Ω₃ does not
affect the successor top from base Ω₃: all transformed bases remain at least
Ω₃, where the existing Y₃ top has image Y₂. -/
theorem vtTopY3_succ_piecewise {S : InaccSeq.{0}}
    {l ηx A X0 e : Ordinal.{0}} (hl : IsRestartIdx l)
    (hX : upsilon l < Nm.Pv S ηx) (hA : A ∈ S.CSet A (S.psi A (Om 1)))
    (hρ : S.psi A (Om 1) = upsilon l)
    (hec : GxCl (upsilon l) (ldAtR S l) e)
    (hT : Rv.RvTop S l (Om (1 + 1 + 1)) (Ug.ugY S)
      (S.psi (Om (1 + 1)) (Om (1 + 1))) e) :
    VtTopDyn S l (Om (1 + 1 + 1)) (Ug.ugY S)
      (fun β => if β < Om (1 + 1 + 1) then X0 else S.psi (Om (1 + 1)) (Om (1 + 1)))
      (e + 1) := by
  apply vtTopDyn_succ_of_stable
    (hs := Vq.vqSh_Y3_rst hl hX hA hρ le_rfl)
    (hl := hl) (hX := hX) (hAo := hA) (hρo := hρ) (hec := hec) (hT := hT)
    (Xhd := fun β => if β < Om (1 + 1 + 1) then X0 else S.psi (Om (1 + 1)) (Om (1 + 1)))
  intro β hb
  simp [not_lt_of_ge hb]

/-- All code exponents at the Y₃ shift have the same dynamic-image transfer
from base Ω₃, even if the chosen image differs below Ω₃. -/
theorem vtTopY3_all_piecewise {S : InaccSeq.{0}}
    {l ηx A X0 : Ordinal.{0}} (hl : IsRestartIdx l)
    (hX : upsilon l < Nm.Pv S ηx) (hA : A ∈ S.CSet A (S.psi A (Om 1)))
    (hρ : S.psi A (Om 1) = upsilon l) :
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
      VtTopDyn S l (Om (1 + 1 + 1)) (Ug.ugY S)
        (fun β => if β < Om (1 + 1 + 1) then X0 else S.psi (Om (1 + 1)) (Om (1 + 1))) e := by
  intro e hec heW
  apply vtTopDyn_of_stable (Vq.vqTopY3E hl hX hA hρ le_rfl e hec heW)
  intro β hb
  simp [not_lt_of_ge hb]

/-- The piecewise Y₃ image has the chosen value at base 0 and Y₂ at base Ω₃. -/
theorem vtY3Image_endpoints {S : InaccSeq.{0}} (X0 : Ordinal.{0}) :
    (if (0 : Ordinal.{0}) < Om (1 + 1 + 1) then X0 else S.psi (Om (1 + 1)) (Om (1 + 1))) = X0 ∧
    (if Om (1 + 1 + 1) < Om (1 + 1 + 1) then X0 else S.psi (Om (1 + 1)) (Om (1 + 1))) =
      S.psi (Om (1 + 1)) (Om (1 + 1)) := by
  constructor
  · rw [if_pos (by
      exact (Om_pos (by norm_num : (1 + 1 + 1 : Ordinal.{0}) ≠ 0)))]
  · rw [if_neg (lt_irrefl _)]

/-- The limit rule for the dynamic-top interface in its constant-image case. -/
theorem vtTopDyn_lim_const {S : InaccSeq.{0}} {l A b X Xh e ηx : Ordinal.{0}}
    (hs : Vq.VqSh S l A b X Xh) (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hAo : A ∈ S.CSet A (S.psi A (Om 1))) (hρo : S.psi A (Om 1) = upsilon l)
    (hlim : IsSuccLimit e) (hec : GxCl (upsilon l) (ldAtR S l) e)
    (heW : e < Om (1 + 1))
    (hIH : ∀ e', GxCl (upsilon l) (ldAtR S l) e' → e' < e → Rv.RvTop S l b X Xh e') :
    VtTopDyn S l b X (fun _ => Xh) e :=
  vtTopDyn_const (Vq.vqTopLim hs hl hX hAo hρo hlim hec heW hIH)

/-- The all-code top rule for the dynamic-top interface in its constant-image case. -/
theorem vtTopDyn_all_const {S : InaccSeq.{0}} {l A b X Xh ηx : Ordinal.{0}}
    (hs : Vq.VqSh S l A b X Xh) (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hAo : A ∈ S.CSet A (S.psi A (Om 1))) (hρo : S.psi A (Om 1) = upsilon l)
    (h0 : Rv.RvTop S l b X Xh 0) :
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
      VtTopDyn S l b X (fun _ => Xh) e := by
  intro e hec heW
  exact vtTopDyn_const (Vq.vqTopE hs hl hX hAo hρo h0 e hec heW)

/-- The pull-back rule for the dynamic-top interface in its constant-image case. -/
theorem vtTopDyn_pull_const {S : InaccSeq.{0}} {l A b X Xh ηx : Ordinal.{0}}
    (hs : Vq.VqSh S l A b X Xh) (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hAo : A ∈ S.CSet A (S.psi A (Om 1))) (hρo : S.psi A (Om 1) = upsilon l)
    (hT : ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → Rv.RvTop S l b X Xh e) :
    VtTopDyn S l b (X + Om (1 + 1)) (fun _ => Xh + Om 1) 0 :=
  vtTopDyn_const (Vq.vqTopW hs hl hX hAo hρo hT)

#print axioms vtTopDyn_const
#print axioms vtTopY3_const
#print axioms vtTopDyn_succ_const
#print axioms vtTopDyn_succ_of_stable
#print axioms vtTopDyn_of_stable
#print axioms vtTopY3_succ_piecewise
#print axioms vtTopY3_all_piecewise
#print axioms vtTopDyn_lim_const
#print axioms vtTopDyn_all_const
#print axioms vtTopDyn_pull_const

end Googology.Trans.PoR.InaccPsi.R2.Vt
