import Googology.Trans.PoR.InaccPsi.R2.VbLaw
import Googology.Trans.PoR.InaccPsi.R2.RjArg
import Googology.Trans.PoR.InaccPsi.R2.LdHull

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ve

open Ordinal
open Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
open Googology.Trans.PoR.InaccPsi.R2
open Googology.Trans.PoR.InaccPsi.R2.Gg
open Googology.Trans.PoR.InaccPsi.R2.Vb
open Googology.Trans.PoR.InaccPsi.R2.Rx
open Googology.Trans.PoR.InaccPsi.R2.Ga
open Googology.Trans.PoR.InaccPsi.R2.Ld
open Googology.Trans.PoR.InaccPsi.R2.Cd
open Googology.Trans.PoR.InaccPsi.R2.Mx
open Googology.Trans.PoR.InaccPsi.R2.Ru
open Googology.Trans.PoR.InaccPsi.R2.Rx

/-- Rewrite powers of `Ω₁` as powers of `ω`. -/
theorem veOm1_pow (a : Ordinal.{0}) : Om1 ^ a = ω ^ (Om1 * a) := by
  have hΩ : Om1 = ω ^ Om1 := by rw [Br.Om1_eq, Bt.Om1_opow]
  conv_lhs => rw [hΩ]
  rw [opow_mul]

/-- Expand a product of an `Ω₁`-power and an `ω`-power. -/
theorem veOm1_pow_mul (a b : Ordinal.{0}) :
    Om1 ^ a * ω ^ b = ω ^ (Om1 * a + b) := by
  rw [veOm1_pow, ← opow_add]

/-- The first shifted exponent law, with an arbitrary countable tail. -/
theorem veK_om1_add {S : InaccSeq.{0}} {l ηx b : Ordinal.{0}}
    (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hbE : RxE S (vbW S l) b) (hb : b < Om1)
    (hxE : RxE S (vbW S l) (Om1 + b)) :
    vbK S l (Om1 + b) = Om 2 + vbK S l b := by
  have hΩ : ω ^ Om1 = Om1 := by
    calc
      ω ^ Om1 = ω ^ Om (1 : Ordinal.{0}) := by rw [Br.Om1_eq]
      _ = Om 1 := Bt.Om1_opow
      _ = Om1 := Br.Om1_eq.symm
  have hbω : b < ω ^ Om1 := by rw [hΩ]; exact hb
  have hKΩ : vbK S l Om1 = Om 2 := by
    change rxL S (upsilon l) (ldAtR S l) (vbW S l) Om1 = Om 2
    have h := rxL_Om (S := S) (Z := upsilon l) (At := ldAtR S l)
      (T := vbW S l) (k := 1) (by norm_num)
    simpa [Br.Om1_eq, one_add_one_eq_two] using h
  rcases eq_or_ne b 0 with rfl | hb0
  · have hK0 : vbK S l 0 = 0 := by
      change rxL S (upsilon l) (ldAtR S l) (vbW S l) 0 = 0
      exact rxL_zero (vbZ hl hX).1
    simpa [hKΩ, hK0]
  · have hrepr : Om1 + b = ω ^ Om1 * 1 + b := by rw [hΩ, mul_one]
    have hlog : log ω (Om1 + b) = Om1 := by
      rw [hrepr]
      rw [log_opow_mul_add one_lt_omega0 one_ne_zero hbω,
        log_eq_zero (by norm_num : (1 : Ordinal.{0}) < ω), add_zero]
    have hdiv : (Om1 + b) / ω ^ Om1 = 1 := by
      rw [hrepr, Ordinal.mul_add_div _ (opow_pos _ omega0_pos).ne',
        Ordinal.div_eq_zero_of_lt hbω, add_zero]
    have hmod : (Om1 + b) % ω ^ Om1 = b := by
      rw [hrepr, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hbω]
    have h1 : Om1 < Om1 + b := lt_add_of_pos_right _ (pos_iff_ne_zero.mpr hb0)
    have h1' : Om 1 < Om1 + b := by simpa [Br.Om1_eq] using h1
    have h3 : log ω (Om1 + b) < Om1 + b := by rw [hlog]; exact h1
    have hmain := rxL_gt (Z := upsilon l) (At := ldAtR S l) (T := vbW S l) hxE h1' h3
    rw [hlog, hdiv, hmod] at hmain
    have hKΩ' : rxL S (upsilon l) (ldAtR S l) (vbW S l) Om1 = Om 2 := hKΩ
    rw [hKΩ', mul_one] at hmain
    have hKb : rxL S (upsilon l) (ldAtR S l) (vbW S l) b = vbK S l b := rfl
    rw [hKb] at hmain
    have hΩ2 : ω ^ Om 2 = Om 2 := gg_SC_eps (SC_Om (by norm_num))
    rw [hΩ2] at hmain
    change rxL S (upsilon l) (ldAtR S l) (vbW S l) (Om1 + b) = _
    exact hmain

/-- Transfer a finite coefficient at the `Ω₁` base. -/
theorem veK_om1_mul_nat {S : InaccSeq.{0}} {l ηx : Ordinal.{0}} (n : ℕ)
    (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hΩE : RxE S (vbW S l) Om1)
    (hn : 1 ≤ n) :
    vbK S l (Om1 * n) = Om 2 * n := by
  have hωΩ : ω ^ Om1 = Om1 := by
    calc
      ω ^ Om1 = ω ^ Om (1 : Ordinal.{0}) := by rw [Br.Om1_eq]
      _ = Om 1 := Bt.Om1_opow
      _ = Om1 := Br.Om1_eq.symm
  have hΩ1 : Om 1 ≤ Om1 := by rw [Br.Om1_eq]
  have hzero : RxE S (vbW S l) 0 := rxE_zero
  have h := (vbK_cnf (S := S) (l := l) hl hX n hn hΩE hzero hΩ1
    (by exact opow_pos _ omega0_pos)).2
  have hrepr : Om1 * n = ω ^ Om1 * n + 0 := by simp [hωΩ]
  have hKΩ : vbK S l Om1 = Om 2 := by
    change rxL S (upsilon l) (ldAtR S l) (vbW S l) Om1 = Om 2
    have hK := rxL_Om (S := S) (Z := upsilon l) (At := ldAtR S l)
      (T := vbW S l) (k := 1) (by norm_num)
    simpa [Br.Om1_eq, one_add_one_eq_two] using hK
  have hωΩ2 : ω ^ Om 2 = Om 2 := gg_SC_eps (SC_Om (by norm_num))
  have hz : vbK S l 0 = 0 := by
    change rxL S (upsilon l) (ldAtR S l) (vbW S l) 0 = 0
    exact rxL_zero (vbZ hl hX).1
  rw [hrepr, h, hKΩ, hz, hωΩ2]
  simp

#print axioms veK_om1_mul_nat

/-- Transfer one `ω`-power term after scaling its exponent by `Ω₁`. -/
theorem veK_om1_opow {S : InaccSeq.{0}} {l ηx c : Ordinal.{0}}
    (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hcE : RxE S (vbW S l) c) (hc : c < Om1)
    (hshiftE : RxE S (vbW S l) (Om1 + c))
    (hpowE : RxE S (vbW S l) (ω ^ (Om1 + c))) :
    vbK S l (Om1 * ω ^ c) = ω ^ (Om 2 + vbK S l c) := by
  have hωΩ : ω ^ Om1 = Om1 := by
    calc
      ω ^ Om1 = ω ^ Om (1 : Ordinal.{0}) := by rw [Br.Om1_eq]
      _ = Om 1 := Bt.Om1_opow
      _ = Om1 := Br.Om1_eq.symm
  have hval : Om1 * ω ^ c = ω ^ (Om1 + c) := by rw [opow_add, hωΩ]
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  have hAt := ldAt_GxAt (S := S) (ConjT.Aη S (cdEta S l)) (upsilon l)
  have hbase : Om 1 ≤ Om1 + c := by
    rw [Br.Om1_eq]
    exact le_self_add
  change rxL S (upsilon l) (ldAtR S l) (vbW S l) (Om1 * ω ^ c) = _
  rw [hval, rxL_opow (Z := upsilon l) (At := ldAtR S l) hZ hZ1 hAt
    hshiftE hpowE hbase]
  change ω ^ vbK S l (Om1 + c) = _
  rw [veK_om1_add hl hX hcE hc hshiftE]

#print axioms veK_om1_opow

/-- The inverse reading preserves `ω`-powers below `Ω₁`. -/
theorem veK_small_opow {S : InaccSeq.{0}} {l ηx c : Ordinal.{0}}
    (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hcE : RxE S (vbW S l) c) (hc : c < Om1)
    (hwE : RxE S (vbW S l) (ω ^ c)) :
    vbK S l (ω ^ c) = ω ^ vbK S l c := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  let At := ldAtR S l
  have hAt : GxAt At := ldAt_GxAt (S := S) (ConjT.Aη S (cdEta S l)) (upsilon l)
  have hOm : Om1 = Om 1 := Br.Om1_eq
  have hc1 : c < Om 1 := by simpa [hOm] using hc
  have hsmallC := rxL_small (Z := upsilon l) (At := At) hZ hZ1 hAt hcE hc1
  have hcΘ : c < gxTh (upsilon l) At (Om 2) := by
    simpa [one_add_one_eq_two] using hsmallC.2.2
  obtain ⟨hcode, hvlt, hread⟩ := ruInv_spec hcΘ
  have hpowSmall : ω ^ c < Om 1 := by simpa [hOm] using Om1_opow_lt hc
  have hsmallW := rxL_small (Z := upsilon l) (At := At) hZ hZ1 hAt hwE hpowSmall
  have hwΘ : ω ^ c < gxTh (upsilon l) At (Om 2) := by
    simpa [one_add_one_eq_two] using hsmallW.2.2
  obtain ⟨hwcode, -, hwread⟩ := ruInv_spec hwΘ
  have hpowCode : GxCl (upsilon l) At (ω ^ ruInv (upsilon l) At c) :=
    GxCl.opow hZ.1 hcode
  have hpowRead : gxTh (upsilon l) At (ω ^ ruInv (upsilon l) At c) = ω ^ c := by
    rw [gxTh_opow hZ hAt hcode, hread]
  have hinv : ruInv (upsilon l) At (ω ^ c) = ω ^ ruInv (upsilon l) At c :=
    ruCode_inj hwcode hpowCode (hwread.trans hpowRead.symm)
  change rxL S (upsilon l) At (vbW S l) (ω ^ c) =
    ω ^ rxL S (upsilon l) At (vbW S l) c
  rw [hsmallW.1, hsmallC.1, hinv]

#print axioms veK_small_opow

/-- The scale law for a single term of the finite `ω`-CNF. -/
theorem veK_scale_opow {S : InaccSeq.{0}} {l ηx c : Ordinal.{0}}
    (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hcE : RxE S (vbW S l) c) (hc : c < Om1)
    (hwE : RxE S (vbW S l) (ω ^ c))
    (hshiftE : RxE S (vbW S l) (Om1 + c))
    (hpowE : RxE S (vbW S l) (ω ^ (Om1 + c))) :
    vbK S l (Om1 * ω ^ c) = Om 2 * vbK S l (ω ^ c) := by
  rw [veK_om1_opow hl hX hcE hc hshiftE hpowE,
    veK_small_opow hl hX hcE hc hwE]
  have hΩ2 : ω ^ Om 2 = Om 2 := gg_SC_eps (SC_Om (by norm_num))
  rw [opow_add, hΩ2]

#print axioms veK_scale_opow

/-- The inverse reading preserves finite coefficients below `Ω₁`. -/
theorem veK_small_mul_nat {S : InaccSeq.{0}} {l ηx c : Ordinal.{0}} (n : ℕ)
    (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hcE : RxE S (vbW S l) c) (hc : c < Om1)
    (hcnE : RxE S (vbW S l) (c * n)) (hcn : c * n < Om1) :
    vbK S l (c * n) = vbK S l c * n := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  let At := ldAtR S l
  have hAt : GxAt At := ldAt_GxAt (S := S) (ConjT.Aη S (cdEta S l)) (upsilon l)
  have hOm : Om1 = Om 1 := Br.Om1_eq
  have hc1 : c < Om 1 := by simpa [hOm] using hc
  have hn1 : c * n < Om 1 := by simpa [hOm] using hcn
  have hsmall := rxL_small (Z := upsilon l) (At := At) hZ hZ1 hAt hcE hc1
  have hsmallN := rxL_small (Z := upsilon l) (At := At) hZ hZ1 hAt hcnE hn1
  obtain ⟨hcode, -, hread⟩ := ruInv_spec hsmall.2.2
  obtain ⟨hcodeN, -, hreadN⟩ := ruInv_spec hsmallN.2.2
  have hmulCode : GxCl (upsilon l) At (ruInv (upsilon l) At c * n) :=
    gx_mul_nat hZ.1 hcode n
  have hmulRead : ∀ k : ℕ, gxTh (upsilon l) At (ruInv (upsilon l) At c * k) = c * k := by
    intro k
    induction k with
    | zero => simp [gxTh_zero]
    | succ k ih =>
      rw [Nat.cast_succ, mul_add_one,
        gxTh_add hZ hAt (gx_mul_nat hZ.1 hcode k), ih, hread,
        mul_add, mul_one]
  have hcodeEq : ruInv (upsilon l) At (c * n) = ruInv (upsilon l) At c * n :=
    gx_inj hcodeN hmulCode (hreadN.trans (hmulRead n).symm)
  change rxL S (upsilon l) At (vbW S l) (c * n) =
    rxL S (upsilon l) At (vbW S l) c * n
  rw [hsmallN.1, hsmall.1, hcodeEq]

#print axioms veK_small_mul_nat

/-- The scale law for one finite-coefficient term of the `ω`-CNF. -/
theorem veK_scale_opow_mul_nat {S : InaccSeq.{0}} {l ηx c : Ordinal.{0}} (n : ℕ)
    (hn : 1 ≤ n) (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hcE : RxE S (vbW S l) c) (hc : c < Om1)
    (hwE : RxE S (vbW S l) (ω ^ c)) (hwnE : RxE S (vbW S l) (ω ^ c * n))
    (hwn : ω ^ c * n < Om1)
    (hshiftE : RxE S (vbW S l) (Om1 + c))
    (hpowE : RxE S (vbW S l) (ω ^ (Om1 + c))) :
    vbK S l (Om1 * (ω ^ c * n)) = Om 2 * vbK S l (ω ^ c * n) := by
  have hωΩ : ω ^ Om1 = Om1 := by
    calc
      ω ^ Om1 = ω ^ Om (1 : Ordinal.{0}) := by rw [Br.Om1_eq]
      _ = Om 1 := Bt.Om1_opow
      _ = Om1 := Br.Om1_eq.symm
  have hbase : Om 1 ≤ Om1 + c := by rw [Br.Om1_eq]; exact le_self_add
  have hscal : Om1 * ω ^ c = ω ^ (Om1 + c) := by rw [opow_add, hωΩ]
  have hzero : RxE S (vbW S l) 0 := rxE_zero
  have hrepr : Om1 * (ω ^ c * n) = ω ^ (Om1 + c) * n + 0 := by
    calc
      Om1 * (ω ^ c * n) = (Om1 * ω ^ c) * n := by rw [← mul_assoc]
      _ = ω ^ (Om1 + c) * n := by rw [hscal]
      _ = _ := (add_zero _).symm
  have hωc1 : ω ^ c < Om1 := Om1_opow_lt hc
  have hcnf := (vbK_cnf (S := S) (l := l) hl hX n hn hshiftE hzero hbase
    (by exact opow_pos _ omega0_pos)).2
  have hΩ2 : ω ^ Om 2 = Om 2 := gg_SC_eps (SC_Om (by norm_num))
  have hz : vbK S l 0 = 0 := by
    change rxL S (upsilon l) (ldAtR S l) (vbW S l) 0 = 0
    exact rxL_zero (vbZ hl hX).1
  rw [hrepr, hcnf, hz]
  simp
  rw [veK_om1_add hl hX hcE hc hshiftE, opow_add, hΩ2]
  rw [veK_small_mul_nat n hl hX hwE hωc1 hwnE hwn]
  rw [veK_small_opow hl hX hcE hc hwE]
  simp [mul_assoc]

#print axioms veK_scale_opow_mul_nat

/-- The inverse reading preserves sums below `Ω₁`. -/
theorem veK_small_add {S : InaccSeq.{0}} {l ηx a b : Ordinal.{0}}
    (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (haE : RxE S (vbW S l) a) (ha : a < Om1)
    (hbE : RxE S (vbW S l) b) (hb : b < Om1)
    (habE : RxE S (vbW S l) (a + b)) (hab : a + b < Om1) :
    vbK S l (a + b) = vbK S l a + vbK S l b := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  let At := ldAtR S l
  have hAt : GxAt At := ldAt_GxAt (S := S) (ConjT.Aη S (cdEta S l)) (upsilon l)
  have hOm : Om1 = Om 1 := Br.Om1_eq
  have ha1 : a < Om 1 := by simpa [hOm] using ha
  have hb1 : b < Om 1 := by simpa [hOm] using hb
  have hab1 : a + b < Om 1 := by simpa [hOm] using hab
  have hsmallA := rxL_small (Z := upsilon l) (At := At) hZ hZ1 hAt haE ha1
  have hsmallB := rxL_small (Z := upsilon l) (At := At) hZ hZ1 hAt hbE hb1
  have hsmallAB := rxL_small (Z := upsilon l) (At := At) hZ hZ1 hAt habE hab1
  obtain ⟨hcodeA, -, hreadA⟩ := ruInv_spec hsmallA.2.2
  obtain ⟨hcodeB, -, hreadB⟩ := ruInv_spec hsmallB.2.2
  obtain ⟨hcodeAB, -, hreadAB⟩ := ruInv_spec hsmallAB.2.2
  have hcodeAdd : GxCl (upsilon l) At (ruInv (upsilon l) At a + ruInv (upsilon l) At b) :=
    GxCl.add hcodeA hcodeB
  have hreadAdd : gxTh (upsilon l) At
      (ruInv (upsilon l) At a + ruInv (upsilon l) At b) = a + b := by
    rw [gxTh_add hZ hAt hcodeA, hreadA, hreadB]
  have hcodeEq : ruInv (upsilon l) At (a + b) =
      ruInv (upsilon l) At a + ruInv (upsilon l) At b :=
    gx_inj hcodeAB hcodeAdd (hreadAB.trans hreadAdd.symm)
  change rxL S (upsilon l) At (vbW S l) (a + b) =
    rxL S (upsilon l) At (vbW S l) a + rxL S (upsilon l) At (vbW S l) b
  rw [hsmallAB.1, hsmallA.1, hsmallB.1, hcodeEq]

#print axioms veK_small_add

/-- One recursive finite-`ω`-CNF step for the `Ω₁` scaling law. -/
theorem veK_scale_cnf_step {S : InaccSeq.{0}} {l ηx c r : Ordinal.{0}} (n : ℕ)
    (hn : 1 ≤ n) (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hcE : RxE S (vbW S l) c) (hc : c < Om1)
    (hwE : RxE S (vbW S l) (ω ^ c))
    (htE : RxE S (vbW S l) (ω ^ c * n)) (ht : ω ^ c * n < Om1)
    (hrE : RxE S (vbW S l) r) (hr : r < Om1)
    (haE : RxE S (vbW S l) (ω ^ c * n + r)) (ha : ω ^ c * n + r < Om1)
    (hshiftE : RxE S (vbW S l) (Om1 + c))
    (hpowE : RxE S (vbW S l) (ω ^ (Om1 + c)))
    (hscaleRE : RxE S (vbW S l) (Om1 * r))
    (hscaleRlt : Om1 * r < ω ^ (Om1 + c))
    (hscaleR : vbK S l (Om1 * r) = Om 2 * vbK S l r) :
    vbK S l (Om1 * (ω ^ c * n + r)) = Om 2 * vbK S l (ω ^ c * n + r) := by
  have hωΩ : ω ^ Om1 = Om1 := by
    calc
      ω ^ Om1 = ω ^ Om (1 : Ordinal.{0}) := by rw [Br.Om1_eq]
      _ = Om 1 := Bt.Om1_opow
      _ = Om1 := Br.Om1_eq.symm
  have hscal : Om1 * ω ^ c = ω ^ (Om1 + c) := by rw [opow_add, hωΩ]
  have hbase : Om 1 ≤ Om1 + c := by rw [Br.Om1_eq]; exact le_self_add
  have hzero : RxE S (vbW S l) 0 := rxE_zero
  have htermScaled : Om1 * (ω ^ c * n) = ω ^ (Om1 + c) * n := by
    rw [← mul_assoc, hscal]
  have htermRepr : Om1 * (ω ^ c * n) = ω ^ (Om1 + c) * n + 0 := by
    rw [htermScaled, add_zero]
  have hargScaled : Om1 * (ω ^ c * n + r) = ω ^ (Om1 + c) * n + Om1 * r := by
    rw [mul_add, htermScaled]
  have hcnf := vbK_cnf (S := S) (l := l) hl hX n hn hshiftE hscaleRE hbase hscaleRlt
  have hzeroK : vbK S l 0 = 0 := by
    change rxL S (upsilon l) (ldAtR S l) (vbW S l) 0 = 0
    exact rxL_zero (vbZ hl hX).1
  have hcnfTerm := (vbK_cnf (S := S) (l := l) hl hX n hn hshiftE
    (rxE_zero : RxE S (vbW S l) 0) hbase (by exact opow_pos _ omega0_pos)).2
  have htermVal : vbK S l (Om1 * (ω ^ c * n)) = ω ^ vbK S l (Om1 + c) * n := by
    rw [htermRepr, hcnfTerm, hzeroK]
    simp
  have hpartScale := veK_scale_opow_mul_nat n hn hl hX hcE hc hwE htE ht hshiftE hpowE
  have htermFormula : ω ^ (Om 2 + vbK S l c) * n = Om 2 * vbK S l (ω ^ c * n) := by
    rw [veK_om1_add hl hX hcE hc hshiftE] at htermVal
    exact htermVal.symm.trans hpartScale
  rw [hargScaled, hcnf.2]
  rw [veK_om1_add hl hX hcE hc hshiftE, htermFormula]
  rw [veK_small_add hl hX htE ht hrE hr haE ha]
  rw [hscaleR, mul_add]

#print axioms veK_scale_cnf_step

/-- The `Ω₁` scaling law for every member below `Ω₁`, by its finite `ω`-CNF. -/
theorem veK_scale_below_Om1 {S : InaccSeq.{0}} {l ηx : Ordinal.{0}}
    (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx) :
    ∀ a, a < Om1 → RxE S (vbW S l) a → RxE S (vbW S l) (Om1 * a) →
      vbK S l (Om1 * a) = Om 2 * vbK S l a := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    intro ha haE hscaleE
    rcases eq_or_ne a 0 with rfl | ha0
    · change rxL S (upsilon l) (ldAtR S l) (vbW S l) (Om1 * 0) =
        Om 2 * rxL S (upsilon l) (ldAtR S l) (vbW S l) 0
      rw [mul_zero]
      rw [rxL_zero (vbZ hl hX).1]
      simp
    · set c := log ω a
      set r := a % ω ^ c
      obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt a one_lt_omega0)
      have hrepr : a = ω ^ c * n + r := by
        dsimp [c, r]
        rw [← hn]
        exact (Ordinal.div_add_mod a (ω ^ c)).symm
      have hcE := (rxE_log haE).1
      have hc_le : c ≤ a := log_le_self ω a
      have hc : c < Om1 := hc_le.trans_lt ha
      have hrE := (rxE_rem haE).1
      have hr_lt : r < ω ^ c := by
        dsimp [r]
        exact Ordinal.mod_lt a (opow_pos c omega0_pos).ne'
      have hrA : r < a := mod_opow_log_lt_self ω ha0
      have hr : r < Om1 := hrA.trans ha
      have hpE := (rxE_lead haE ha0).1
      have hn1 : 1 ≤ n := by
        have hpowle : ω ^ c ≤ a := opow_log_le_self ω ha0
        rcases Nat.eq_zero_or_pos n with hn0 | hnp
        · have hlt : a < ω ^ c := by
            calc
              a = ω ^ c * 0 + r := by rw [hrepr, hn0]; simp
              _ = r := by simp
              _ < ω ^ c := hr_lt
          exact False.elim ((not_lt_of_ge hpowle) hlt)
        · exact hnp
      have ht : ω ^ c * n < Om1 := by
        have htle : ω ^ c * n ≤ a := by rw [hrepr]; exact le_self_add
        exact htle.trans_lt ha
      have htE : RxE S (vbW S l) (ω ^ c * n) := by
        refine ⟨RxN.mul_nat hpE.1 n, ConjT.mul_nat_mem S hpE.2.1 n, ?_⟩
        exact (show ω ^ c * n ≤ a from by rw [hrepr]; exact le_self_add).trans_lt haE.2.2
      have hsumE : RxE S (vbW S l) (ω ^ c * n + r) := by simpa [hrepr] using haE
      have hsum : ω ^ c * n + r < Om1 := by simpa [hrepr] using ha
      have hΩ : ω ^ Om1 = Om1 := by
        calc
          ω ^ Om1 = ω ^ Om (1 : Ordinal.{0}) := by rw [Br.Om1_eq]
          _ = Om 1 := Bt.Om1_opow
          _ = Om1 := Br.Om1_eq.symm
      have hscal : Om1 * ω ^ c = ω ^ (Om1 + c) := by rw [opow_add, hΩ]
      have hscaleRlt : Om1 * r < ω ^ (Om1 + c) := by
        calc
          Om1 * r < Om1 * ω ^ c := by
            apply mul_lt_mul_of_pos_left hr_lt
            rw [Br.Om1_eq]
            exact Om_pos one_ne_zero
          _ = ω ^ (Om1 + c) := hscal
      have hscaleArg : Om1 * a = ω ^ (Om1 + c) * n + Om1 * r := by
        rw [hrepr, mul_add, ← mul_assoc, hscal]
      have hn0 : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hlogScale : log ω (Om1 * a) = Om1 + c := by
        rw [hscaleArg, log_opow_mul_add one_lt_omega0 hn0 hscaleRlt,
          log_eq_zero (natCast_lt_omega0 n), add_zero]
      have hremScale : (Om1 * a) % ω ^ log ω (Om1 * a) = Om1 * r := by
        rw [hlogScale, hscaleArg, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hscaleRlt]
      have hlogMem := (rxE_log hscaleE).1
      rw [hlogScale] at hlogMem
      have hremMem := (rxE_rem hscaleE).1
      rw [hremScale] at hremMem
      have hscale0 : Om1 * a ≠ 0 := by
        apply (mul_pos ?_ (pos_iff_ne_zero.mpr ha0)).ne'
        rw [Br.Om1_eq]
        exact Om_pos one_ne_zero
      have hpowMem := (rxE_lead hscaleE hscale0).1
      rw [hlogScale] at hpowMem
      have hrec := ih r hrA hr hrE hremMem
      have hresult := veK_scale_cnf_step n hn1 hl hX hcE hc hpE htE ht hrE hr hsumE hsum
        hlogMem hpowMem hremMem hscaleRlt hrec
      rw [← hrepr] at hresult
      exact hresult

#print axioms veK_scale_below_Om1

/-- One finite-`ω`-CNF step for the exponent law with an additive tail. -/
theorem veK_exponent_cnf_step {S : InaccSeq.{0}} {l ηx c r b : Ordinal.{0}} (n : ℕ)
    (hn : 1 ≤ n) (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hcE : RxE S (vbW S l) c) (hc : c < Om1)
    (hwE : RxE S (vbW S l) (ω ^ c))
    (htE : RxE S (vbW S l) (ω ^ c * n)) (ht : ω ^ c * n < Om1)
    (hrE : RxE S (vbW S l) r) (hr : r < Om1)
    (haE : RxE S (vbW S l) (ω ^ c * n + r)) (ha : ω ^ c * n + r < Om1)
    (hb : b < Om1)
    (hshiftE : RxE S (vbW S l) (Om1 + c))
    (hpowE : RxE S (vbW S l) (ω ^ (Om1 + c)))
    (hscaleRE : RxE S (vbW S l) (Om1 * r + b))
    (hscaleRlt : Om1 * r + b < ω ^ (Om1 + c))
    (hscaleR : vbK S l (Om1 * r + b) = Om 2 * vbK S l r + vbK S l b) :
    vbK S l (Om1 * (ω ^ c * n + r) + b) =
      Om 2 * vbK S l (ω ^ c * n + r) + vbK S l b := by
  have hωΩ : ω ^ Om1 = Om1 := by
    calc
      ω ^ Om1 = ω ^ Om (1 : Ordinal.{0}) := by rw [Br.Om1_eq]
      _ = Om 1 := Bt.Om1_opow
      _ = Om1 := Br.Om1_eq.symm
  have hscal : Om1 * ω ^ c = ω ^ (Om1 + c) := by rw [opow_add, hωΩ]
  have hbase : Om 1 ≤ Om1 + c := by rw [Br.Om1_eq]; exact le_self_add
  have hzero : RxE S (vbW S l) 0 := rxE_zero
  have htermScaled : Om1 * (ω ^ c * n) = ω ^ (Om1 + c) * n := by
    rw [← mul_assoc, hscal]
  have htermRepr : Om1 * (ω ^ c * n) = ω ^ (Om1 + c) * n + 0 := by
    rw [htermScaled, add_zero]
  have hargScaled : Om1 * (ω ^ c * n + r) + b =
      ω ^ (Om1 + c) * n + (Om1 * r + b) := by
    rw [mul_add, htermScaled, add_assoc]
  have hcnf := vbK_cnf (S := S) (l := l) hl hX n hn hshiftE hscaleRE hbase hscaleRlt
  have hzeroK : vbK S l 0 = 0 := by
    change rxL S (upsilon l) (ldAtR S l) (vbW S l) 0 = 0
    exact rxL_zero (vbZ hl hX).1
  have hcnfTerm := (vbK_cnf (S := S) (l := l) hl hX n hn hshiftE
    (rxE_zero : RxE S (vbW S l) 0) hbase (by exact opow_pos _ omega0_pos)).2
  have htermVal : vbK S l (Om1 * (ω ^ c * n)) = ω ^ vbK S l (Om1 + c) * n := by
    rw [htermRepr, hcnfTerm, hzeroK]
    simp
  have hpartScale := veK_scale_opow_mul_nat n hn hl hX hcE hc hwE htE ht hshiftE hpowE
  have htermFormula : ω ^ (Om 2 + vbK S l c) * n = Om 2 * vbK S l (ω ^ c * n) := by
    rw [veK_om1_add hl hX hcE hc hshiftE] at htermVal
    exact htermVal.symm.trans hpartScale
  rw [hargScaled, hcnf.2]
  rw [veK_om1_add hl hX hcE hc hshiftE, htermFormula, hscaleR,
    veK_small_add hl hX htE ht hrE hr haE ha]
  rw [mul_add]
  simp [add_assoc]

#print axioms veK_exponent_cnf_step

/-- The shifted exponent law for every `a,b<Ω₁`, by finite `ω`-CNF induction. -/
theorem veK_exponent_add_below_Om1 {S : InaccSeq.{0}} {l ηx : Ordinal.{0}}
    (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx) :
    ∀ a b, a < Om1 → b < Om1 → RxE S (vbW S l) a →
      RxE S (vbW S l) (Om1 * a + b) →
      vbK S l (Om1 * a + b) = Om 2 * vbK S l a + vbK S l b := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    intro b ha hb haE hscaleE
    rcases eq_or_ne a 0 with rfl | ha0
    · simp only [mul_zero, zero_add]
      change rxL S (upsilon l) (ldAtR S l) (vbW S l) b =
        Om 2 * rxL S (upsilon l) (ldAtR S l) (vbW S l) 0 +
          rxL S (upsilon l) (ldAtR S l) (vbW S l) b
      rw [rxL_zero (vbZ hl hX).1]
      simp
    · set c := log ω a
      set r := a % ω ^ c
      obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt a one_lt_omega0)
      have hrepr : a = ω ^ c * n + r := by
        dsimp [c, r]
        rw [← hn]
        exact (Ordinal.div_add_mod a (ω ^ c)).symm
      have hcE := (rxE_log haE).1
      have hc_le : c ≤ a := log_le_self ω a
      have hc : c < Om1 := hc_le.trans_lt ha
      have hrE := (rxE_rem haE).1
      have hr_lt : r < ω ^ c := by
        dsimp [r]
        exact Ordinal.mod_lt a (opow_pos c omega0_pos).ne'
      have hrA : r < a := mod_opow_log_lt_self ω ha0
      have hr : r < Om1 := hrA.trans ha
      have hpE := (rxE_lead haE ha0).1
      have hn1 : 1 ≤ n := by
        have hpowle : ω ^ c ≤ a := opow_log_le_self ω ha0
        rcases Nat.eq_zero_or_pos n with hn0 | hnp
        · have hlt : a < ω ^ c := by
            calc
              a = ω ^ c * 0 + r := by rw [hrepr, hn0]; simp
              _ = r := by simp
              _ < ω ^ c := hr_lt
          exact False.elim ((not_lt_of_ge hpowle) hlt)
        · exact hnp
      have ht : ω ^ c * n < Om1 := by
        have htle : ω ^ c * n ≤ a := by rw [hrepr]; exact le_self_add
        exact htle.trans_lt ha
      have htE : RxE S (vbW S l) (ω ^ c * n) := by
        refine ⟨RxN.mul_nat hpE.1 n, ConjT.mul_nat_mem S hpE.2.1 n, ?_⟩
        exact (show ω ^ c * n ≤ a from by rw [hrepr]; exact le_self_add).trans_lt haE.2.2
      have hsumE : RxE S (vbW S l) (ω ^ c * n + r) := by simpa [hrepr] using haE
      have hsum : ω ^ c * n + r < Om1 := by simpa [hrepr] using ha
      have hΩ : ω ^ Om1 = Om1 := by
        calc
          ω ^ Om1 = ω ^ Om (1 : Ordinal.{0}) := by rw [Br.Om1_eq]
          _ = Om 1 := Bt.Om1_opow
          _ = Om1 := Br.Om1_eq.symm
      have hscal : Om1 * ω ^ c = ω ^ (Om1 + c) := by rw [opow_add, hΩ]
      have hscaleRlt : Om1 * r + b < ω ^ (Om1 + c) := by
        have hmulR : Om1 * r < ω ^ (Om1 + c) := by
          calc
            Om1 * r < Om1 * ω ^ c := by
              apply mul_lt_mul_of_pos_left hr_lt
              rw [Br.Om1_eq]
              exact Om_pos one_ne_zero
            _ = ω ^ (Om1 + c) := hscal
        have hbPow : b < ω ^ (Om1 + c) := by
          apply hb.trans_le
          calc
            Om1 = ω ^ Om1 := hΩ.symm
            _ ≤ ω ^ (Om1 + c) :=
              opow_le_opow_right (zero_lt_one.trans one_lt_omega0) le_self_add
        exact (indec_opow (Om1 + c)).add_lt hmulR hbPow
      have hscaleArg : Om1 * a + b =
          ω ^ (Om1 + c) * n + (Om1 * r + b) := by
        calc
          Om1 * a + b = Om1 * (ω ^ c * n + r) + b := by rw [hrepr]
          _ = (Om1 * (ω ^ c * n) + Om1 * r) + b := by rw [mul_add]
          _ = ω ^ (Om1 + c) * n + (Om1 * r + b) := by
            rw [add_assoc, ← mul_assoc, hscal]
      have hn0 : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hlogScale : log ω (Om1 * a + b) = Om1 + c := by
        rw [hscaleArg, log_opow_mul_add one_lt_omega0 hn0 hscaleRlt,
          log_eq_zero (natCast_lt_omega0 n), add_zero]
      have hremScale : (Om1 * a + b) % ω ^ log ω (Om1 * a + b) = Om1 * r + b := by
        rw [hlogScale, hscaleArg, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hscaleRlt]
      have hlogMem := (rxE_log hscaleE).1
      rw [hlogScale] at hlogMem
      have hremMem := (rxE_rem hscaleE).1
      rw [hremScale] at hremMem
      have hscale0 : Om1 * a + b ≠ 0 := by
        apply (lt_of_lt_of_le (mul_pos ?_ (pos_iff_ne_zero.mpr ha0)) le_self_add).ne'
        rw [Br.Om1_eq]
        exact Om_pos one_ne_zero
      have hpowMem := (rxE_lead hscaleE hscale0).1
      rw [hlogScale] at hpowMem
      have hrec := ih r hrA b hr hb hrE hremMem
      have hzero : RxE S (vbW S l) 0 := rxE_zero
      have hbase : Om 1 ≤ Om1 + c := by rw [Br.Om1_eq]; exact le_self_add
      have hcnf := vbK_cnf (S := S) (l := l) hl hX n hn1 hlogMem hremMem hbase hscaleRlt
      have hzeroK : vbK S l 0 = 0 := by
        change rxL S (upsilon l) (ldAtR S l) (vbW S l) 0 = 0
        exact rxL_zero (vbZ hl hX).1
      have htermRepr : Om1 * (ω ^ c * n) = ω ^ (Om1 + c) * n + 0 := by
        calc
          Om1 * (ω ^ c * n) = (Om1 * ω ^ c) * n := by rw [← mul_assoc]
          _ = ω ^ (Om1 + c) * n := by rw [hscal]
          _ = _ := (add_zero _).symm
      have hcnfTerm := (vbK_cnf (S := S) (l := l) hl hX n hn1 hlogMem hzero hbase
        (by exact opow_pos _ omega0_pos)).2
      have htermVal : vbK S l (Om1 * (ω ^ c * n)) = ω ^ vbK S l (Om1 + c) * n := by
        rw [htermRepr, hcnfTerm, hzeroK]
        simp
      have hpartScale := veK_scale_opow_mul_nat n hn1 hl hX hcE hc hpE htE ht hlogMem hpowMem
      have htermFormula : ω ^ (Om 2 + vbK S l c) * n = Om 2 * vbK S l (ω ^ c * n) := by
        rw [veK_om1_add hl hX hcE hc hlogMem] at htermVal
        exact htermVal.symm.trans hpartScale
      have htotal := veK_exponent_cnf_step n hn1 hl hX hcE hc hpE htE ht hrE hr hsumE hsum hb
        hlogMem hpowMem hremMem hscaleRlt hrec
      rw [← hrepr] at htotal
      exact htotal

#print axioms veK_exponent_add_below_Om1

/-- Rewrite powers of `Ω₂` as powers of `ω`. -/
theorem veOm2_pow (a : Ordinal.{0}) : Om 2 ^ a = ω ^ (Om 2 * a) := by
  have hΩ : Om 2 = ω ^ Om 2 := (gg_SC_eps (SC_Om (by norm_num))).symm
  conv_lhs => rw [hΩ]
  rw [opow_mul]

/-- A finite-coefficient normal-form term at exponent `Ω₁*a+b`. -/
theorem veK_coeff_cnf_term {S : InaccSeq.{0}} {l ηx a b t : Ordinal.{0}} (n : ℕ)
    (hn : 1 ≤ n) (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (ha : a < Om1) (hb : b < Om1) (haE : RxE S (vbW S l) a)
    (hdE : RxE S (vbW S l) (Om1 * a + b))
    (hpowE : RxE S (vbW S l) (ω ^ (Om1 * a + b)))
    (htE : RxE S (vbW S l) t) (ht : t < ω ^ (Om1 * a + b))
    (hbase : Om 1 ≤ Om1 * a + b) :
    vbK S l (ω ^ (Om1 * a + b) * n + t) =
      Om 2 ^ vbK S l a * ω ^ vbK S l b * n + vbK S l t := by
  have hshift := veK_exponent_add_below_Om1 hl hX a b ha hb haE hdE
  have hcnf := (vbK_cnf (S := S) (l := l) hl hX n hn hdE htE hbase ht).2
  rw [hshift] at hcnf
  have hpow : ω ^ (Om1 * a + b) = ω ^ (Om1 * a) * ω ^ b := by rw [opow_add]
  have hpowVal : ω ^ (Om 2 * vbK S l a + vbK S l b) =
      Om 2 ^ vbK S l a * ω ^ vbK S l b := by
    rw [opow_add, ← veOm2_pow]
  rw [hpowVal] at hcnf
  exact hcnf

#print axioms veK_coeff_cnf_term

/-- Transfer a finite coefficient with a small additive remainder. -/
theorem veK_coeff_tail_finite {S : InaccSeq.{0}} {l ηx a t : Ordinal.{0}} (n : ℕ)
    (hn : 1 ≤ n) (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (ha : a < Om1) (ha0 : 0 < a) (haE : RxE S (vbW S l) a)
    (hdE : RxE S (vbW S l) (Om1 * a))
    (hpowE : RxE S (vbW S l) (ω ^ (Om1 * a)))
    (htE : RxE S (vbW S l) t) (ht : t < ω ^ (Om1 * a)) :
    vbK S l (ω ^ (Om1 * a) * n + t) = Om 2 ^ vbK S l a * n + vbK S l t := by
  have hbase' : Om1 ≤ Om1 * a := le_mul_left _ ha0
  have hbase : Om 1 ≤ Om1 * a := Br.Om1_eq ▸ hbase'
  have hOmpos : 0 < Om1 := by rw [Br.Om1_eq]; exact Om_pos one_ne_zero
  have hterm := veK_coeff_cnf_term (a := a) (b := (0 : Ordinal.{0})) (t := t)
    n hn hl hX ha hOmpos haE (by simpa [add_zero] using hdE)
    (by simpa [add_zero] using hpowE) htE (by simpa [add_zero] using ht)
    (by simpa [add_zero] using hbase)
  have hzero : vbK S l 0 = 0 := by
    change rxL S (upsilon l) (ldAtR S l) (vbW S l) 0 = 0
    exact rxL_zero (vbZ hl hX).1
  simpa [hzero] using hterm

#print axioms veK_coeff_tail_finite

/-- Transfer an arbitrary coefficient below `Ω₁` by its finite `ω`-CNF. -/
theorem veK_coeff_below_Om1 {S : InaccSeq.{0}} {l ηx a : Ordinal.{0}}
    (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (ha : a < Om1) (haE : RxE S (vbW S l) a) :
    ∀ c, c < Om1 → RxE S (vbW S l) c →
      RxE S (vbW S l) (ω ^ (Om1 * a) * c) →
      vbK S l (ω ^ (Om1 * a) * c) = Om 2 ^ vbK S l a * vbK S l c := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c ih =>
    intro hc hcE hscaleE
    rcases eq_or_ne a 0 with ha0 | ha0
    · subst a
      simp only [mul_zero, opow_zero, one_mul]
      change rxL S (upsilon l) (ldAtR S l) (vbW S l) c =
        Om 2 ^ vbK S l 0 * rxL S (upsilon l) (ldAtR S l) (vbW S l) c
      have hzero : vbK S l 0 = 0 := by
        change rxL S (upsilon l) (ldAtR S l) (vbW S l) 0 = 0
        exact rxL_zero (vbZ hl hX).1
      rw [hzero]
      simp
    · rcases eq_or_ne c 0 with rfl | hc0
      · simp only [mul_zero, rxL_zero (vbZ hl hX).1]
      · set b := log ω c
        set r := c % ω ^ b
        obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt c one_lt_omega0)
        have hrepr : c = ω ^ b * n + r := by
          dsimp [b, r]
          rw [← hn]
          exact (Ordinal.div_add_mod c (ω ^ b)).symm
        have hbE := (rxE_log hcE).1
        have hb_le : b ≤ c := log_le_self ω c
        have hb : b < Om1 := hb_le.trans_lt hc
        have hrE := (rxE_rem hcE).1
        have hr_lt : r < ω ^ b := by
          dsimp [r]
          exact Ordinal.mod_lt c (opow_pos b omega0_pos).ne'
        have hrA : r < c := mod_opow_log_lt_self ω hc0
        have hr : r < Om1 := hrA.trans hc
        have hpE := (rxE_lead hcE hc0).1
        have hn1 : 1 ≤ n := by
          have hpowle : ω ^ b ≤ c := opow_log_le_self ω hc0
          rcases Nat.eq_zero_or_pos n with hn0 | hnp
          · have hlt : c < ω ^ b := by
              calc
                c = ω ^ b * 0 + r := by rw [hrepr, hn0]; simp
                _ = r := by simp
                _ < ω ^ b := hr_lt
            exact False.elim ((not_lt_of_ge hpowle) hlt)
          · exact hnp
        have ht : ω ^ b * n < Om1 := by
          have htle : ω ^ b * n ≤ c := by rw [hrepr]; exact le_self_add
          exact htle.trans_lt hc
        have htE : RxE S (vbW S l) (ω ^ b * n) := by
          refine ⟨RxN.mul_nat hpE.1 n, ConjT.mul_nat_mem S hpE.2.1 n, ?_⟩
          exact (show ω ^ b * n ≤ c from by rw [hrepr]; exact le_self_add).trans_lt hcE.2.2
        have hsumE : RxE S (vbW S l) (ω ^ b * n + r) := by simpa [hrepr] using hcE
        have hsum : ω ^ b * n + r < Om1 := by simpa [hrepr] using hc
        have hApos : 0 < Om1 * a := mul_pos (by rw [Br.Om1_eq]; exact Om_pos one_ne_zero)
          (pos_iff_ne_zero.mpr ha0)
        have hA1 : Om1 ≤ Om1 * a := le_mul_left Om1 (pos_iff_ne_zero.mpr ha0)
        have hbase : Om 1 ≤ Om1 * a + b := by
          calc
            Om 1 = Om1 := Br.Om1_eq.symm
            _ ≤ Om1 * a := hA1
            _ ≤ Om1 * a + b := le_self_add
        have hOmega : ω ^ Om1 = Om1 := by
          calc
            ω ^ Om1 = ω ^ Om (1 : Ordinal.{0}) := by rw [Br.Om1_eq]
            _ = Om 1 := Bt.Om1_opow
            _ = Om1 := Br.Om1_eq.symm
        have hpowBound : Om1 ≤ ω ^ (Om1 * a + b) := by
          calc
            Om1 = ω ^ Om1 := hOmega.symm
            _ ≤ ω ^ (Om1 * a + b) :=
              opow_le_opow_right (zero_lt_one.trans one_lt_omega0)
                (hA1.trans le_self_add)
        have hscaleRlt : ω ^ (Om1 * a) * r < ω ^ (Om1 * a + b) := by
          calc
            ω ^ (Om1 * a) * r < ω ^ (Om1 * a) * ω ^ b :=
              mul_lt_mul_of_pos_left hr_lt (opow_pos _ omega0_pos)
            _ = ω ^ (Om1 * a + b) := by rw [opow_add]
        have hscalTerm : ω ^ (Om1 * a) * (ω ^ b * n) = ω ^ (Om1 * a + b) * n := by
          rw [← mul_assoc, opow_add]
        have hscaleArg : ω ^ (Om1 * a) * c =
            ω ^ (Om1 * a + b) * n + ω ^ (Om1 * a) * r := by
          calc
            ω ^ (Om1 * a) * c = ω ^ (Om1 * a) * (ω ^ b * n + r) := by rw [hrepr]
            _ = (ω ^ (Om1 * a) * (ω ^ b * n)) + ω ^ (Om1 * a) * r := by rw [mul_add]
            _ = ω ^ (Om1 * a + b) * n + ω ^ (Om1 * a) * r := by rw [hscalTerm]
        have hn0 : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
        have hlogScale : log ω (ω ^ (Om1 * a) * c) = Om1 * a + b := by
          rw [hscaleArg, log_opow_mul_add one_lt_omega0 hn0 hscaleRlt,
            log_eq_zero (natCast_lt_omega0 n), add_zero]
        have hremScale : (ω ^ (Om1 * a) * c) % ω ^ log ω (ω ^ (Om1 * a) * c) =
            ω ^ (Om1 * a) * r := by
          rw [hlogScale, hscaleArg, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hscaleRlt]
        have hlogMem := (rxE_log hscaleE).1
        rw [hlogScale] at hlogMem
        have hremMem := (rxE_rem hscaleE).1
        rw [hremScale] at hremMem
        have hscale0 : ω ^ (Om1 * a) * c ≠ 0 := by
          exact (mul_pos (opow_pos _ omega0_pos) (pos_iff_ne_zero.mpr hc0)).ne'
        have hpowMem := (rxE_lead hscaleE hscale0).1
        rw [hlogScale] at hpowMem
        have hrec := ih r hrA hr hrE hremMem
        have hterm := veK_coeff_cnf_term n hn1 hl hX ha hb haE hlogMem hpowMem hremMem
          (hscaleRlt) hbase
        have hsmallAdd := veK_small_add hl hX htE ht hrE hr hsumE hsum
        have hsmallMul := veK_small_mul_nat n hl hX hpE
          (by exact Om1_opow_lt hb) htE ht
        have hsmallPow := veK_small_opow hl hX hbE hb hpE
        have hcoeff : vbK S l c = ω ^ vbK S l b * n + vbK S l r := by
          rw [hrepr, hsmallAdd, hsmallMul, hsmallPow]
        rw [hscaleArg, hterm, hrec, hcoeff]
        rw [mul_add]
        simp [mul_assoc, add_assoc]

#print axioms veK_coeff_below_Om1

/-- Transfer an arbitrary small coefficient together with a small additive tail. -/
theorem veK_coeff_below_Om1_add {S : InaccSeq.{0}} {l ηx a s : Ordinal.{0}}
    (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (ha : a < Om1) (haE : RxE S (vbW S l) a)
    (hs : s < Om1) (hsE : RxE S (vbW S l) s) :
    ∀ c, c < Om1 → RxE S (vbW S l) c →
      RxE S (vbW S l) (ω ^ (Om1 * a) * c + s) →
      vbK S l (ω ^ (Om1 * a) * c + s) = Om 2 ^ vbK S l a * vbK S l c + vbK S l s := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c ih =>
    intro hc hcE hwholeE
    rcases eq_or_ne a 0 with ha0 | ha0
    · subst a
      have hsum : c + s < Om1 := Om1_add_lt hc hs
      have hsumE : RxE S (vbW S l) (c + s) := by simpa using hwholeE
      have hsmall := veK_small_add hl hX hcE hc hsE hs hsumE hsum
      have hzero : vbK S l 0 = 0 := by
        change rxL S (upsilon l) (ldAtR S l) (vbW S l) 0 = 0
        exact rxL_zero (vbZ hl hX).1
      simpa [hzero] using hsmall
    · rcases eq_or_ne c 0 with rfl | hc0
      · have hzero : vbK S l 0 = 0 := by
          change rxL S (upsilon l) (ldAtR S l) (vbW S l) 0 = 0
          exact rxL_zero (vbZ hl hX).1
        simp [hzero]
      · set b := log ω c
        set r := c % ω ^ b
        obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt c one_lt_omega0)
        have hrepr : c = ω ^ b * n + r := by
          dsimp [b, r]
          rw [← hn]
          exact (Ordinal.div_add_mod c (ω ^ b)).symm
        have hbE := (rxE_log hcE).1
        have hb_le : b ≤ c := log_le_self ω c
        have hb : b < Om1 := hb_le.trans_lt hc
        have hrE := (rxE_rem hcE).1
        have hr_lt : r < ω ^ b := by
          dsimp [r]
          exact Ordinal.mod_lt c (opow_pos b omega0_pos).ne'
        have hrA : r < c := mod_opow_log_lt_self ω hc0
        have hr : r < Om1 := hrA.trans hc
        have hpE := (rxE_lead hcE hc0).1
        have hn1 : 1 ≤ n := by
          have hpowle : ω ^ b ≤ c := opow_log_le_self ω hc0
          rcases Nat.eq_zero_or_pos n with hn0 | hnp
          · have hlt : c < ω ^ b := by
              calc
                c = ω ^ b * 0 + r := by rw [hrepr, hn0]; simp
                _ = r := by simp
                _ < ω ^ b := hr_lt
            exact False.elim ((not_lt_of_ge hpowle) hlt)
          · exact hnp
        have ht : ω ^ b * n < Om1 := by
          have htle : ω ^ b * n ≤ c := by rw [hrepr]; exact le_self_add
          exact htle.trans_lt hc
        have htE : RxE S (vbW S l) (ω ^ b * n) := by
          refine ⟨RxN.mul_nat hpE.1 n, ConjT.mul_nat_mem S hpE.2.1 n, ?_⟩
          exact (show ω ^ b * n ≤ c from by rw [hrepr]; exact le_self_add).trans_lt hcE.2.2
        have hsumE : RxE S (vbW S l) (ω ^ b * n + r) := by simpa [hrepr] using hcE
        have hsum : ω ^ b * n + r < Om1 := by simpa [hrepr] using hc
        have hApos : 0 < Om1 * a := mul_pos (by rw [Br.Om1_eq]; exact Om_pos one_ne_zero)
          (pos_iff_ne_zero.mpr ha0)
        have hA1 : Om1 ≤ Om1 * a := le_mul_left Om1 (pos_iff_ne_zero.mpr ha0)
        have hbase : Om 1 ≤ Om1 * a + b := by
          calc
            Om 1 = Om1 := Br.Om1_eq.symm
            _ ≤ Om1 * a := hA1
            _ ≤ Om1 * a + b := le_self_add
        have hOmega : ω ^ Om1 = Om1 := by
          calc
            ω ^ Om1 = ω ^ Om (1 : Ordinal.{0}) := by rw [Br.Om1_eq]
            _ = Om 1 := Bt.Om1_opow
            _ = Om1 := Br.Om1_eq.symm
        have hpowBound : Om1 ≤ ω ^ (Om1 * a + b) := by
          calc
            Om1 = ω ^ Om1 := hOmega.symm
            _ ≤ ω ^ (Om1 * a + b) :=
              opow_le_opow_right (zero_lt_one.trans one_lt_omega0)
                (hA1.trans le_self_add)
        have hscaleRlt : ω ^ (Om1 * a) * r < ω ^ (Om1 * a + b) := by
          calc
            ω ^ (Om1 * a) * r < ω ^ (Om1 * a) * ω ^ b :=
              mul_lt_mul_of_pos_left hr_lt (opow_pos _ omega0_pos)
            _ = ω ^ (Om1 * a + b) := by rw [opow_add]
        have htailLt : ω ^ (Om1 * a) * r + s < ω ^ (Om1 * a + b) := by
          have hsmallD : s < ω ^ (Om1 * a) := by
            have hD : Om1 ≤ Om1 * a := hA1
            have hOmD : Om1 ≤ ω ^ (Om1 * a) := by
              calc
                Om1 = ω ^ Om1 := hOmega.symm
                _ ≤ ω ^ (Om1 * a) := opow_le_opow_right
                  (zero_lt_one.trans one_lt_omega0) hD
            exact hs.trans_le hOmD
          have hlt : ω ^ (Om1 * a) * r + s < ω ^ (Om1 * a) * r + ω ^ (Om1 * a) :=
            (add_lt_add_iff_left _).2 hsmallD
          have hmul : ω ^ (Om1 * a) * r + ω ^ (Om1 * a) =
              ω ^ (Om1 * a) * (r + 1) := by rw [mul_add]; simp
          have hr1 : r + 1 ≤ ω ^ b := Order.add_one_le_of_lt hr_lt
          calc
            ω ^ (Om1 * a) * r + s < ω ^ (Om1 * a) * (r + 1) := by rw [← hmul]; exact hlt
            _ ≤ ω ^ (Om1 * a) * ω ^ b := mul_le_mul_left' hr1 _
            _ = ω ^ (Om1 * a + b) := by rw [opow_add]
        have hscalTerm : ω ^ (Om1 * a) * (ω ^ b * n) = ω ^ (Om1 * a + b) * n := by
          rw [← mul_assoc, opow_add]
        have hscaleArg : ω ^ (Om1 * a) * c + s =
            ω ^ (Om1 * a + b) * n + (ω ^ (Om1 * a) * r + s) := by
          calc
            ω ^ (Om1 * a) * c + s = ω ^ (Om1 * a) * (ω ^ b * n + r) + s := by rw [hrepr]
            _ = (ω ^ (Om1 * a) * (ω ^ b * n) + ω ^ (Om1 * a) * r) + s := by rw [mul_add]
            _ = ω ^ (Om1 * a + b) * n + (ω ^ (Om1 * a) * r + s) := by rw [hscalTerm, add_assoc]
        have hn0 : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
        have hlogScale : log ω (ω ^ (Om1 * a) * c + s) = Om1 * a + b := by
          rw [hscaleArg, log_opow_mul_add one_lt_omega0 hn0 htailLt,
            log_eq_zero (natCast_lt_omega0 n), add_zero]
        have hremScale : (ω ^ (Om1 * a) * c + s) % ω ^ log ω (ω ^ (Om1 * a) * c + s) =
            ω ^ (Om1 * a) * r + s := by
          rw [hlogScale, hscaleArg, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt htailLt]
        have hlogMem := (rxE_log hwholeE).1
        rw [hlogScale] at hlogMem
        have hremMem := (rxE_rem hwholeE).1
        rw [hremScale] at hremMem
        have hwhole0 : ω ^ (Om1 * a) * c + s ≠ 0 := by
          exact (lt_of_lt_of_le
            (mul_pos (opow_pos _ omega0_pos) (pos_iff_ne_zero.mpr hc0)) le_self_add).ne'
        have hpowMem := (rxE_lead hwholeE hwhole0).1
        rw [hlogScale] at hpowMem
        have hrec := ih r hrA hr hrE hremMem
        have hterm := veK_coeff_cnf_term n hn1 hl hX ha hb haE hlogMem hpowMem
          hremMem htailLt hbase
        have hsmallAdd := veK_small_add hl hX htE ht hrE hr hsumE hsum
        have hsmallMul := veK_small_mul_nat n hl hX hpE
          (by exact Om1_opow_lt hb) htE ht
        have hsmallPow := veK_small_opow hl hX hbE hb hpE
        have hcoeff : vbK S l c = ω ^ vbK S l b * n + vbK S l r := by
          rw [hrepr, hsmallAdd, hsmallMul, hsmallPow]
        rw [hscaleArg, hterm, hrec, hcoeff]
        rw [mul_add]
        simp [mul_assoc, add_assoc]

#print axioms veK_coeff_below_Om1_add

/-- The base-`Ω₁` normal-form transfer, in `Ω₁`-power notation. -/
theorem veK_Om1_pow_coeff_add {S : InaccSeq.{0}} {l ηx a s : Ordinal.{0}}
    (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (ha : a < Om1) (haE : RxE S (vbW S l) a)
    (hs : s < Om1) (hsE : RxE S (vbW S l) s) {c : Ordinal.{0}}
    (hc : c < Om1) (hcE : RxE S (vbW S l) c)
    (hwhole : RxE S (vbW S l) (Om1 ^ a * c + s)) :
    vbK S l (Om1 ^ a * c + s) = Om 2 ^ vbK S l a * vbK S l c + vbK S l s := by
  simpa only [veOm1_pow] using
    (veK_coeff_below_Om1_add hl hX ha haE hs hsE c hc hcE (by simpa only [veOm1_pow] using hwhole))

#print axioms veK_Om1_pow_coeff_add

#print axioms veK_om1_add

#print axioms veOm1_pow
#print axioms veOm1_pow_mul

end Googology.Trans.PoR.InaccPsi.R2.Ve
