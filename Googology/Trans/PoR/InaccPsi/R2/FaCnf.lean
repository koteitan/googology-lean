import Googology.Trans.PoR.InaccPsi.R2.FaVt
import Googology.Trans.PoR.InaccPsi.R2.AwCan
import Googology.Trans.PoR.InaccPsi.R2.ZaFrag
import Googology.Trans.PoR.InaccPsi.R2.XiHull

/-!
# Fa: FRAG MOVES THE READINGS ABOVE `θ` (the first part: the Cantor normal form of a code, for any atoms)

`fc_mul_nat`, `fc_Rd_mul_nat`, `fc_parts_code`, `fc_Rd_cnf`, `fc_exps_code`, `fc_zkEx_Rd`, `fc_zkCnf`: the lemmas `Aw.aw_*` for any atoms `At`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Fa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Zr Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xi
  Googology.Trans.PoR.InaccPsi.R2.Qf Googology.Trans.PoR.InaccPsi.R2.Zk Googology.Trans.PoR.InaccPsi.R2.Un
  Googology.Trans.PoR.InaccPsi.R2.Vi Googology.Trans.PoR.InaccPsi.R2.Vl Googology.Trans.PoR.InaccPsi.R2.Xj
  Googology.Trans.PoR.InaccPsi.R2.Aw

variable {S : InaccSeq.{0}}

section Cnf

variable {y : Ordinal.{0}} {At : Set Ordinal.{0}} (hy : SC y) (hAt : GxAt At)
include hy hAt

theorem fc_mul_nat {u : Ordinal.{0}} (hu : GxCl y At u) : ∀ n : ℕ, GxCl y At (u * n)
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact GxCl.zero hy.1
  | n + 1 => by
    rw [Nat.cast_succ, mul_add_one]
    exact GxCl.add (fc_mul_nat hu n) hu

theorem fc_Rd_mul_nat {u : Ordinal.{0}} (hu : GxCl y At u) :
    ∀ n : ℕ, gxTh y At (u * n) = gxTh y At u * n
  | 0 => by rw [Nat.cast_zero, mul_zero, mul_zero, gxTh_zero]
  | n + 1 => by
    rw [Nat.cast_succ, mul_add_one, mul_add_one, gxTh_add hy hAt (fc_mul_nat hy hAt hu n),
      fc_Rd_mul_nat hu n]

/-- The parts of a code `ω^c·k + r` are codes. -/
theorem fc_parts_code {c k r : Ordinal.{0}} (hk0 : k ≠ 0) (hk : k < ω) (hr : r < ω ^ c)
    (ha : GxCl y At (ω ^ c * k + r)) : GxCl y At c ∧ GxCl y At r := by
  obtain ⟨-, hl, -, -⟩ := zk_parts hk0 hk hr
  have hcc : GxCl y At c := by
    have := (gxDec hy hAt _ ha).2
    rwa [hl] at this
  refine ⟨hcc, ?_⟩
  obtain ⟨n, rfl⟩ := lt_omega0.1 hk
  have := (gxDec hy hAt _ ha).1 _ (fc_mul_nat hy hAt (hcc.opow hy.1) n) le_self_add
  rwa [Ordinal.add_sub_cancel] at this

/-- **The reading on the Cantor normal form.** -/
theorem fc_Rd_cnf {c k r : Ordinal.{0}} (hk : k < ω) (hc : GxCl y At c) (hrc : GxCl y At r)
    (hr : r < ω ^ c) :
    gxTh y At (ω ^ c * k + r) = ω ^ gxTh y At c * k + gxTh y At r ∧
      gxTh y At r < ω ^ gxTh y At c := by
  obtain ⟨n, rfl⟩ := lt_omega0.1 hk
  have hop := gxTh_opow hy hAt hc
  constructor
  · rw [gxTh_add hy hAt (fc_mul_nat hy hAt (hc.opow hy.1) n), fc_Rd_mul_nat hy hAt (hc.opow hy.1) n, hop]
  · rw [← hop]; exact gxTh_lt hrc hr

/-- The Cantor exponents of a code are codes, in a finite set. -/
theorem fc_exps_code (hy1 : y < Om1) : ∀ a, GxCl y At a →
    ∃ E : Finset Ordinal.{0}, (∀ w ∈ E, GxCl y At w ∧ w ≤ a) ∧ ZkEx (· ∈ E) a := by
  classical
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro ha
  rcases eq_or_ne a 0 with rfl | h0
  · exact ⟨∅, by simp, zkEx_zero _⟩
  obtain ⟨hk0, hk, hr, he⟩ := zk_dec h0
  rw [← he] at ha
  obtain ⟨hlc, hrc⟩ := fc_parts_code hy hAt hk0 hk hr ha
  have hlt := mod_opow_log_lt_self ω h0
  obtain ⟨E, hE1, hE2⟩ := IH _ hlt hrc
  refine ⟨insert (log ω a) E, fun w hw => ?_, ?_⟩
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨hlc, log_le_self _ _⟩
    · exact ⟨(hE1 w hw).1, (hE1 w hw).2.trans hlt.le⟩
  · rw [zkEx_ne _ h0]
    exact ⟨Finset.mem_insert_self _ _, zkEx_mono (fun w hw => Finset.mem_insert_of_mem hw) _ hE2⟩

/-- A property of the readings of the exponents of a code is a property of the exponents of its reading. -/
theorem fc_zkEx_Rd {P : Ordinal.{0} → Prop} : ∀ a, GxCl y At a →
    ZkEx (fun e => P (gxTh y At e)) a → ZkEx P (gxTh y At a) := by
  refine zk_ind (fun _ _ => by rw [gxTh_zero]; exact zkEx_zero _) ?_
  intro c k r hk0 hk hr IH ha hE
  obtain ⟨hcc, hrc⟩ := fc_parts_code hy hAt hk0 hk hr ha
  obtain ⟨e1, e2⟩ := fc_Rd_cnf hy hAt hk hcc hrc hr
  rw [zkEx_step _ hk0 hk hr] at hE
  rw [e1, zkEx_step _ hk0 hk e2]
  exact ⟨hE.1, IH hrc hE.2⟩

end Cnf

/-- **The exponent map of `f` sends the reading at `ρ` to the reading at `σ`** when it does on the exponents. -/
theorem fc_zkCnf {ρ σ : Ordinal.{0}} {At At' : Set Ordinal.{0}} (hρ : SC ρ) (hAt : GxAt At) (hσ : SC σ) (hAt' : GxAt At') {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ a, GxCl ρ At a → GxCl σ At' a →
      ZkEx (fun e => f (gxTh ρ At e) = gxTh σ At' e) a →
      zkCnf f (gxTh ρ At a) = gxTh σ At' a := by
  refine zk_ind (fun _ _ _ => by rw [gxTh_zero, gxTh_zero, zkCnf_zero]) ?_
  intro c k r hk0 hk hr IH ha hb hE
  obtain ⟨hcc, hrc⟩ := fc_parts_code hρ hAt hk0 hk hr ha
  obtain ⟨hcc', hrc'⟩ := fc_parts_code hσ hAt' hk0 hk hr hb
  obtain ⟨e1, e2⟩ := fc_Rd_cnf hρ hAt hk hcc hrc hr
  obtain ⟨e1', -⟩ := fc_Rd_cnf hσ hAt' hk hcc' hrc' hr
  rw [zkEx_step _ hk0 hk hr] at hE
  rw [e1, e1', zkCnf_step f hk0 hk e2, hE.1, IH hrc hrc' hE.2]

end Googology.Trans.PoR.InaccPsi.R2.Fa
