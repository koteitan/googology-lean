import Googology.Trans.PoR.InaccPsi.R2.VbLaw
import Googology.Trans.PoR.InaccPsi.R2.UgPart

/-! Small overlap lemmas for the inverse image and the recursive reading. -/

namespace Googology.Trans.PoR.InaccPsi.R2.Ve

open Ordinal Order Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
open Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Ug
open Googology.Trans.PoR.InaccPsi.R2.Tx
open Googology.Trans.PoR.InaccPsi.R2.Tg

variable {S : InaccSeq.{0}} {l ηx : Ordinal.{0}}

theorem veT_eq_ugTh_code (hl : IsRestartIdx l)
    (hX : upsilon l < Nm.Pv S ηx) {x : Ordinal.{0}}
    (hx : VbD S l x) (hx2 : x < Om (1 + 1)) :
    vbT S l x = ugTh S l x := by
  rw [vbT_code hl hX hx2 hx.1]
  rw [ugTh_lt (hx2.trans (Ua.uaGam_spec.2))]
  exact (Ua.uaThCode hl hX hx2).symm

/-- Agreement also holds at the first level boundary, `Ω₂`. -/
theorem veT_eq_ugTh_Om2 (hl : IsRestartIdx l)
    (hX : upsilon l < Nm.Pv S ηx) :
    vbT S l (Om (1 + 1)) = ugTh S l (Om (1 + 1)) := by
  have hT := vbT_Om hl hX (k := 1) (by norm_num)
  have hT' : vbT S l (Om (1 + 1)) = Om 1 := by simpa using hT
  rw [hT']
  rw [ugTh_lt Ua.uaGam_spec.2, Ua.uaTh_lt Tg.tgOm_lt_G, Tx.txOm2 hl hX]

#print axioms veT_eq_ugTh_Om2

end Googology.Trans.PoR.InaccPsi.R2.Ve
