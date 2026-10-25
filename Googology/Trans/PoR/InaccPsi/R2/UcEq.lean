import Googology.Trans.PoR.InaccPsi.R2.UcUB
import Googology.Trans.PoR.InaccPsi.R2.TsPsi

/-!
# The `ψ_{Ω₂} ↔ H_γ` lemma at every level `γ < ε_{Ω₂+1}`: `ψ_{Ω₂}(B + Ω₂^γ·D) = H_γ(c + D)`

`ψ = ψ_{Ω₂} = S.psi · Ω₂`, `W^γ = Ω₂^γ`, `E₂ = ucE = ε_{Ω₂+1}`, `H_γ = Uc.ucH γ`, `ucC γ` the largest component of
`γ`, `UcLt q x` (all components of `x` below `q`).  An argument `B` is *own* when `B ∈ Cl(B, ψ(B))`.  This is
`R2.TsPsi` (levels `β < Ω₂`, `F_β`) for every level `γ < E₂` with `H_γ`; the closure under the lower levels is asked
only for the levels `j` with `ucC j` below the value (the definition of `H_γ`), and the hull is read through the
components (`R2.UcUB`).

* `uc_leWe` (`Le.leWe γ = Ω₂^γ`), `uc_mem` (**the hull converse**: `x < E₂` with all components below `b` and `Ω₂·x`
  lie in `Cl(a, b)`), `uc_W_mem` (`Ω₂^γ·D ∈ Cl(a, b)`), `ucLt_succ`, `ucC_le_succ`, `uc_own_comps` (**the components
  of an own `B < E₂` are below `ψ(B)`**);
* `UcFWD`, `UcCONV`, `uc_fwd_conv` (**FWD(γ)**: `ψ(B)` is a fixed point of `H_γ` for every own `B ≠ 0` with
  `Ω₂^{γ+1} ∣ B` and `ucC γ < ψ(B)`; **CONV(γ)**: `Ω₂^{γ+1} ∣ B` for every own `B < E₂` with `ψ(B)` a fixed point of
  `H_γ`; at every level `γ < E₂`);
* `uc_eq` (**`ψ(B + Ω₂^γ·D) = H_γ(c + D)` and `D < ψ(B + Ω₂^γ·D)`** for an own `B < E₂` with `Ω₂^γ ∣ B`, `H_γ(c) =
  ψ(B)`, `D < Ω₂` with `d < H_γ(c + d)` for every `d ≤ D`, given FWD below `γ`), `uc_eq_all` (FWD discharged),
  `uc_psiU_mul_all` (**`ψ(Ω₂^γ·(1 + D)) = H_γ(c + D)`** for `H_γ(c) = ψ(Ω₂^γ)`, `ucC γ < ψ(Ω₂^γ)`).

No new axiom.  New definitions: the statement names `UcFWD`, `UcCONV`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Rh

variable {S : InaccSeq.{0}}

theorem uc_leWe (γ : Ordinal.{0}) : Le.leWe γ = OmTwo ^ γ := by
  unfold Le.leWe; rw [uc_W_eq, uc_Om2_eq]

/-- **The hull converse**: `x < E₂` with all components below `b > 0` lies in `Cl(a, b)`, and so does `Ω₂·x`. -/
theorem uc_mem {a b : Ordinal.{0}} (hb : 0 < b) :
    ∀ x, x < ucE → UcLt b x → x ∈ S.CSet a b ∧ Om (1 + 1) * x ∈ S.CSet a b := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxE hx
  by_cases hx2 : x < OmTwo
  · have hxb := (ucLt_small hx2).1 hx
    exact ⟨CSet.of_lt hxb, Ts.tsOm2_mul_mem hxb⟩
  have hx2' := not_lt.1 hx2
  have hx0 : x ≠ 0 := uc_ne_zero hx2'
  set e := log OmTwo x with hedef
  set d := x / OmTwo ^ e with hddef
  set r := x % OmTwo ^ e with hrdef
  have he1 : 1 ≤ e := one_le_iff_ne_zero.2 (log_pos uc_one_lt_Om2 hx0 hx2').ne'
  have hcnf : OmTwo ^ e * d + r = x := uc_cnf_eq x
  have hr : r < OmTwo ^ e := Ordinal.mod_lt _ (uc_W_pos e).ne'
  have hd : d < OmTwo := uc_div_lt x
  have hd0 : d ≠ 0 := (uc_div_pos hx2').ne'
  have hx' := hx
  rw [← hcnf, ucLt_cnf he1 hd0 hd hr (by rw [hcnf]; exact hxE)] at hx'
  obtain ⟨hxe, hdb, hxr⟩ := hx'
  have hel := uc_log_lt hx2' hxE
  have hrl := uc_mod_lt hx2'
  obtain ⟨-, heM⟩ := IH e hel (hel.trans hxE) hxe
  obtain ⟨hrM, hrM2⟩ := IH r hrl (hrl.trans hxE) hxr
  have hW : OmTwo ^ e * d ∈ S.CSet a b := by
    rw [uc_W_eq, uc_Om2_eq]; exact Nm.mem_opow_mul heM hdb
  have hW2 : Om (1 + 1) * (OmTwo ^ e * d) ∈ S.CSet a b := by
    have h1 : Om (1 + 1) * (OmTwo ^ e * d) = ω ^ (Om (1 + 1) + Om (1 + 1) * e) * d := by
      rw [← uc_Om2_eq, ← mul_assoc]
      have h2 : (OmTwo : Ordinal.{0}) * OmTwo ^ e = OmTwo ^ (1 + e) := by rw [opow_add, opow_one]
      rw [h2, uc_W_eq, mul_add, mul_one]
    rw [h1]; exact Nm.mem_opow_mul (CSet.add_mem (Mx.mxOm2_mem _ _) heM) hdb
  refine ⟨?_, ?_⟩
  · rw [← hcnf]; exact CSet.add_mem hW hrM
  · rw [← hcnf, mul_add]; exact CSet.add_mem hW2 hrM2

/-- `Ω₂^γ·D ∈ Cl(a, b)` for `γ < E₂` with all components below `b`, `D < b`. -/
theorem uc_W_mem {a b γ D : Ordinal.{0}} (hγ : γ < ucE) (hγb : UcLt b γ) (hD : D < b) :
    OmTwo ^ γ * D ∈ S.CSet a b := by
  rw [uc_W_eq, uc_Om2_eq]; exact Nm.mem_opow_mul (uc_mem (zero_le.trans_lt hD) γ hγ hγb).2 hD

theorem ucLt_succ {q x : Ordinal.{0}} (hq : SC q) (hE : x + 1 < ucE) (hx : UcLt q x) : UcLt q (x + 1) :=
  ucLt_add hq hE hx ((ucLt_small uc_one_lt_Om2).2 (uc_one_lt_SC hq))

/-- `ucC j ≤ ucC (j + 1)`. -/
theorem ucC_le_succ : ∀ j : Ordinal.{0}, ucC j ≤ ucC (j + 1) := by
  intro j
  induction j using WellFoundedLT.induction with
  | ind j IH =>
  by_cases h1 : j < OmTwo
  · rw [ucC_small h1, ucC_small (uc_SC_Om2.add_one_lt h1)]; exact le_self_add
  by_cases h2 : j + 1 < ucE
  · have hjE : j < ucE := (lt_add_one j).trans h2
    have h1' := not_lt.1 h1
    set e := log OmTwo j with hedef
    set d := j / OmTwo ^ e with hddef
    set r := j % OmTwo ^ e with hrdef
    have he1 : 1 ≤ e := one_le_iff_ne_zero.2 (log_pos uc_one_lt_Om2 (uc_ne_zero h1') h1').ne'
    have hcnf : OmTwo ^ e * d + r = j := uc_cnf_eq j
    have hr : r < OmTwo ^ e := Ordinal.mod_lt _ (uc_W_pos e).ne'
    have hr1 : r + 1 < OmTwo ^ e := (uc_W_indec e).add_lt hr
      ((uc_one_lt_Om2).trans_le ((opow_one (OmTwo : Ordinal.{0})).symm.trans_le
        ((opow_le_opow_iff_right uc_one_lt_Om2).2 he1)))
    have hd : d < OmTwo := uc_div_lt j
    have hd0 : d ≠ 0 := (uc_div_pos h1').ne'
    have e1 : j + 1 = OmTwo ^ e * d + (r + 1) := by rw [← add_assoc, hcnf]
    unfold ucC
    rw [e1, ucFold_cnf id he1 hd0 hd hr1 (by rw [← e1]; exact h2)]
    conv_lhs => rw [← hcnf, ucFold_cnf id he1 hd0 hd hr (by rw [hcnf]; exact hjE)]
    exact max_le_max le_rfl (max_le_max le_rfl (IH r (uc_mod_lt h1')))
  · have hj : ucE ≤ j := by
      by_contra h; exact h2 (uc_E_indec (not_le.1 h) (uc_one_lt_Om2.trans ucE_gt))
    unfold ucC; rw [ucFold_out id hj]; exact zero_le


/-- **The components of an own `B < E₂` are below `ψ(B)`.** -/
theorem uc_own_comps {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (1 + 1)))) (hBE : B < ucE) :
    UcLt (S.psi B (Om (1 + 1))) B := by
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  have hq2 : S.psi B (Om (1 + 1)) < OmTwo := by rw [uc_Om2_eq]; exact Ts.ts_psi_lt B
  refine uc_hull (Ts.ts_psi_SC B) (Ts.ts_Om1_lt_psi B) hq2 hBE.le (fun e he heC _ => ?_) B hown
  exact lt_psi_of_mem hκ (CSet.psi_mem he hκ (mem_CSet_psi hκ B) heC) (psi_lt hκ _)

/-! ## The fixed-point statements -/

/-- **FWD(γ)**: `ψ(B)` is a fixed point of `H_γ` for every own `B ≠ 0` with `Ω₂^{γ+1} ∣ B` and `ucC γ < ψ(B)`. -/
def UcFWD (S : InaccSeq.{0}) (γ : Ordinal.{0}) : Prop :=
  ∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om (1 + 1))) → OmTwo ^ (γ + 1) ∣ B → B ≠ 0 →
    ucC γ < S.psi B (Om (1 + 1)) → ucH γ (S.psi B (Om (1 + 1))) = S.psi B (Om (1 + 1))

/-- **CONV(γ)**: `Ω₂^{γ+1} ∣ B` for every own `B < E₂` with `ψ(B)` a fixed point of `H_γ`. -/
def UcCONV (S : InaccSeq.{0}) (γ : Ordinal.{0}) : Prop :=
  ∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om (1 + 1))) → B < ucE →
    ucH γ (S.psi B (Om (1 + 1))) = S.psi B (Om (1 + 1)) → OmTwo ^ (γ + 1) ∣ B

theorem uc_fwd0 : UcFWD S 0 := by
  intro B hown hB hB0 _
  rw [zero_add, opow_one, uc_Om2_eq] at hB
  have h := Ts.ts_fix0 hown hB hB0
  have hv : max Om1 0 < S.psi B (Om (1 + 1)) := by
    rw [max_eq_left zero_le, Rj.rj_Om1]; exact Ts.ts_Om1_lt_psi B
  exact (ucH_fix_iff_F uc_SC_Om2.1 hv).2 (by rw [rhF_zero]; exact h)

/-- **FWD(γ) and CONV(γ) at every level `γ < E₂`.** -/
theorem uc_fwd_conv : ∀ γ : Ordinal.{0}, γ < ucE → UcFWD S γ ∧ UcCONV S γ := by
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  have hO := uc_Om2_eq
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ
  constructor
  · -- FWD
    intro B hown hB hB0 hCx
    rcases eq_or_ne γ 0 with rfl | hγ0
    · exact uc_fwd0 B hown hB hB0 hCx
    set x := S.psi B (Om (1 + 1)) with hxdef
    have hx2 : x < Om (1 + 1) := Ts.ts_psi_lt B
    have hxSC : SC x := Ts.ts_psi_SC B
    have hx1 : Om 1 < x := Ts.ts_Om1_lt_psi B
    have hxΓ : gamma x = x := by
      have h1 : OmTwo ^ ((0 : Ordinal.{0}) + 1) ∣ B :=
        (opow_dvd_opow _ (by rw [zero_add]; exact one_le_iff_ne_zero.2 (by
          rw [← Order.one_le_iff_ne_zero]; exact le_add_self))).trans hB
      have h0 : ucC 0 < x := by rw [ucC_small uc_SC_Om2.1]; exact hxSC.1
      have h2 := (IH 0 (pos_iff_ne_zero.2 hγ0) (uc_SC_Om2.1.trans ucE_gt)).1 B hown h1 hB0 h0
      have hv : max Om1 0 < x := by rw [max_eq_left zero_le, Rj.rj_Om1]; exact hx1
      have h3 := (ucH_fix_iff_F uc_SC_Om2.1 hv).1 h2
      rwa [rhF_zero] at h3
    have hlimx : IsSuccLimit x := hxSC.isSuccLimit
    set u := OmTwo ^ γ with hudef
    have hu0 : u ≠ 0 := (uc_W_pos γ).ne'
    have hupos : 0 < u := uc_W_pos γ
    obtain ⟨m, hm⟩ := hB
    rw [uc_W_succ, ← hudef, mul_assoc] at hm
    have hγLt : ∀ w, ucC γ < w → UcLt w γ := fun w hw => (ucC_lt_iff (zero_le.trans_lt hw) γ).1 hw
    have key : ∀ z < x, ucH γ z < x := by
      intro z hz
      have hxI : Indec x := Lq.lq_SC_indec hxSC
      set a := Om 1 + ucC γ + z + 1 with hadef
      have hax : a < x := hxSC.add_one_lt (hxI.add_lt (hxI.add_lt hx1 hCx) hz)
      set p := gamma a with hpdef
      have hpx : p < x := by rw [← hxΓ]; exact gamma_lt_gamma.2 hax
      have hpSC : SC p := Lq.lq_gamma_SC a
      have hap : a < p :=
        lt_of_le_of_ne (Lq.lq_le_gamma a) fun e => SC.ne_add_one hpSC (Om 1 + ucC γ + z) e.symm
      have hCp : ucC γ < p := by
        refine lt_of_le_of_lt ?_ hap
        rw [hadef]; exact le_add_self.trans (le_self_add.trans le_self_add)
      have hz1p : z + 1 < p := by
        refine lt_of_le_of_lt ?_ hap
        rw [hadef, add_assoc]; exact le_add_self
      have hp1 : Om 1 < p := by
        refine lt_of_le_of_lt ?_ hap
        rw [hadef]; exact le_self_add.trans (le_self_add.trans le_self_add)
      obtain ⟨Bp, hownp, hBpB, hpBp, -⟩ := Ts.ts_own_below_lt hown hpSC hp1 hpx
      set e := u * (Bp / u) + u with hedef
      have hBpe : Bp ≤ e := by
        calc Bp = u * (Bp / u) + Bp % u := (Ordinal.div_add_mod Bp u).symm
          _ ≤ e := add_le_add_right (Ordinal.mod_lt Bp hu0).le _
      have hpe : p ≤ S.psi e (Om (1 + 1)) := hpBp.trans (psi_mono hκ hBpe).1
      have hCe : ucC γ < S.psi e (Om (1 + 1)) := hCp.trans_le hpe
      have hBpmem : Bp ∈ S.CSet e (S.psi e (Om (1 + 1))) := (psi_mono hκ hBpe).2 hownp
      have hmod : u * (Bp / u) ∈ S.CSet e (S.psi e (Om (1 + 1))) := by
        have := Ts.ts_mod_mem (S := S) (one_le_iff_ne_zero.2 hγ0) Bp hBpmem
        rwa [uc_leWe] at this
      have huM : u ∈ S.CSet e (S.psi e (Om (1 + 1))) := by
        have := uc_W_mem (S := S) (a := e) hγ (hγLt _ hCe) (uc_one_lt_SC (Ts.ts_psi_SC e))
        rwa [mul_one] at this
      have howne : e ∈ S.CSet e (S.psi e (Om (1 + 1))) := CSet.add_mem hmod huM
      have hue : u ∣ e := ⟨Bp / u + 1, by rw [hedef, mul_add, mul_one]⟩
      have hue0 : 0 < e := lt_of_lt_of_le hupos le_add_self
      have hed : ∀ d, d < S.psi e (Om (1 + 1)) →
          e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om (1 + 1))) ∧
            ∃ w, ucH γ w = S.psi (e + u * d) (Om (1 + 1)) := by
        intro d hd
        have hle : S.psi e (Om (1 + 1)) ≤ S.psi (e + u * d) (Om (1 + 1)) := (psi_mono hκ le_self_add).1
        have hownd : e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om (1 + 1))) :=
          CSet.add_mem ((psi_mono hκ le_self_add).2 howne)
            (uc_W_mem hγ (hγLt _ (hCe.trans_le hle)) (hd.trans_le hle))
        refine ⟨hownd, ucG_range (Ts.ts_psi_SC _) (by rw [Rj.rj_Om1]; exact Ts.ts_Om1_lt_psi _)
          (hCe.trans_le hle) fun j hj hcj => ?_⟩
        exact (IH j hj (hj.trans hγ)).1 _ hownd
          ((opow_dvd_opow _ (Order.add_one_le_of_lt hj)).trans (dvd_add hue (dvd_mul_right _ _)))
          (lt_of_lt_of_le hue0 le_self_add).ne' hcj
      have hmono : ∀ d d', d < d' → d' < S.psi e (Om (1 + 1)) →
          S.psi (e + u * d) (Om (1 + 1)) < S.psi (e + u * d') (Om (1 + 1)) := fun d d' hdd hd' =>
        Ts.ts_psi_lt_of_own (hed d (hdd.trans hd')).1
          ((add_lt_add_iff_left e).2 ((mul_lt_mul_iff_right₀ hupos).2 hdd))
      have hcount : ∀ d, d < S.psi e (Om (1 + 1)) → ∀ w, ucH γ w = S.psi (e + u * d) (Om (1 + 1)) →
          d ≤ w := by
        intro d
        induction d using WellFoundedLT.induction with
        | ind d IHd =>
        intro hd w hw
        by_contra hwd
        push Not at hwd
        obtain ⟨w', hw'⟩ := (hed w (hwd.trans hd)).2
        have h1 := IHd w hwd (hwd.trans hd) w' hw'
        have h2 : ucH γ w' < ucH γ w := by rw [hw', hw]; exact hmono w d hwd hd
        exact absurd ((ucH_lt_iff γ).1 h2) (not_lt.2 h1)
      have hz1e : z + 1 < S.psi e (Om (1 + 1)) := hz1p.trans_le hpe
      obtain ⟨w, hw⟩ := (hed (z + 1) hz1e).2
      have hzw : z < w := (lt_add_one z).trans_le (hcount (z + 1) hz1e w hw)
      have hlt : e + u * (z + 1) < B := by
        have hq : Bp / u < OmTwo * m := by
          rw [hm] at hBpB; exact (Ordinal.lt_mul_iff_div_lt hu0).1 hBpB
        have hx2' : x < OmTwo := by rw [hO]; exact hx2
        have hc1 : 1 + (z + 1) < OmTwo :=
          (Lq.lq_SC_indec uc_SC_Om2).add_lt uc_one_lt_Om2 (uc_SC_Om2.add_one_lt (hz.trans hx2'))
        have e1 : e + u * (z + 1) = u * (Bp / u + (1 + (z + 1))) := by
          simp only [hedef, mul_add, mul_one, add_assoc]
        rw [e1, hm]
        exact (mul_lt_mul_iff_right₀ hupos).2
          (Rd.rd_add_lt_of_dvd (Lq.lq_SC_indec uc_SC_Om2) (dvd_mul_right _ _) hq hc1)
      have hψlt : S.psi (e + u * (z + 1)) (Om (1 + 1)) < x :=
        psi_lt_psi_of_mem hκ hlt ((psi_mono hκ hlt.le).2 (hed (z + 1) hz1e).1)
      calc ucH γ z < ucH γ w := (ucH_lt_iff γ).2 hzw
        _ = _ := hw
        _ < x := hψlt
    exact le_antisymm (((ucH_normal γ).le_iff_forall_le hlimx).2 fun z hz => (key z hz).le)
      (ucH_le_self γ x)
  · -- CONV
    intro B hown hBE hfix
    set p := S.psi B (Om (1 + 1)) with hpdef
    have hpSC : SC p := Ts.ts_psi_SC B
    have hcomp : UcLt p B := uc_own_comps hown hBE
    have hu : OmTwo ^ γ ∣ B := by
      rcases zero_or_succ_or_isSuccLimit γ with hz | ⟨j, rfl⟩ | hl
      · rw [hz, opow_zero]; exact one_dvd B
      · rw [Order.succ_eq_add_one] at hfix hγ ⊢
        have hC1 := ucH_C_lt (j + 1) p
        rw [hfix] at hC1
        have hCj : ucC j < p := (ucC_le_succ j).trans_lt hC1
        have hfixj : ucH j p = p := ucG_fix_mono le_self_add hfix hCj
        exact (IH j (Order.lt_succ j) ((lt_add_one j).trans hγ)).2 B hown hBE hfixj
      · by_contra hnd
        have hR0 : B % OmTwo ^ γ ≠ 0 := fun h => hnd (Ordinal.dvd_of_mod_eq_zero h)
        have hRlt : B % OmTwo ^ γ < OmTwo ^ γ := Ordinal.mod_lt _ (uc_W_pos γ).ne'
        have hRc : UcLt p (B % OmTwo ^ γ) := (ucLt_div_mod hpSC.1 hBE hcomp γ).2
        have hRE : B % OmTwo ^ γ < ucE := hRlt.trans (uc_W_lt_E hγ)
        set R := B % OmTwo ^ γ with hRdef
        set j0 := log OmTwo R with hj0
        have hj0l : j0 < γ := by
          have h1 : OmTwo ^ j0 ≤ R := opow_log_le_self _ hR0
          exact (opow_lt_opow_iff_right uc_one_lt_Om2).1 (h1.trans_lt hRlt)
        have hj0c : UcLt p j0 := by
          rcases lt_or_ge R OmTwo with hR2 | hR2
          · rw [hj0, log_eq_zero hR2]; exact ucLt_zero hpSC.1
          · have hcn := ucLt_cnf (q := p) (one_le_iff_ne_zero.2 (log_pos uc_one_lt_Om2 hR0 hR2).ne')
              (uc_div_pos hR2).ne' (uc_div_lt R) (Ordinal.mod_lt _ (uc_W_pos _).ne')
              (by rw [uc_cnf_eq]; exact hRE)
            rw [uc_cnf_eq] at hcn
            exact (hcn.1 hRc).1
        have hj1l : j0 + 1 < γ := hl.add_one_lt hj0l
        have hj1E : j0 + 1 < ucE := hj1l.trans hγ
        have hj1c : ucC (j0 + 1) < p := (ucC_lt_iff hpSC.1 _).2 (ucLt_succ hpSC hj1E hj0c)
        have hfixj : ucH (j0 + 1) p = p := ucG_fix_mono hj1l.le hfix hj1c
        have hdiv := (IH (j0 + 1) hj1l hj1E).2 B hown hBE hfixj
        have hd2 : OmTwo ^ (j0 + 1 + 1) ∣ OmTwo ^ γ * (B / OmTwo ^ γ) :=
          (opow_dvd_opow _ (Order.add_one_le_of_lt hj1l)).trans (dvd_mul_right _ _)
        have hdR : OmTwo ^ (j0 + 1 + 1) ∣ R := by
          have h := hdiv
          rw [← Ordinal.div_add_mod B (OmTwo ^ γ)] at h
          exact (Ordinal.dvd_add_iff hd2).1 h
        have h1 : OmTwo ^ (j0 + 1 + 1) ≤ R := Ordinal.le_of_dvd hR0 hdR
        have h2 : R < OmTwo ^ (j0 + 1) := lt_opow_succ_log_self uc_one_lt_Om2 R
        have h3 : OmTwo ^ (j0 + 1) ≤ OmTwo ^ (j0 + 1 + 1) := opow_le_opow_right uc_SC_Om2.1 le_self_add
        exact absurd (h3.trans h1) (not_le.2 h2)
    set u := OmTwo ^ γ with hudef
    set u2 := OmTwo ^ (γ + 1) with hu2def
    have hu2 : u2 = u * OmTwo := uc_W_succ γ
    have huu2 : u ∣ u2 := opow_dvd_opow _ le_self_add
    have hupos : 0 < u := uc_W_pos γ
    have hu0 : u ≠ 0 := hupos.ne'
    obtain ⟨m, hm⟩ := hu
    by_contra hnd
    set D0 := m % OmTwo with hD0
    set B0 := u2 * (m / OmTwo) with hB0
    have hBe : B0 + u * D0 = B := by
      rw [hm, hB0, hD0, hu2, mul_assoc, ← mul_add, Ordinal.div_add_mod]
    have hD0lt : D0 < OmTwo := Ordinal.mod_lt m uc_SC_Om2.1.ne'
    have hD00 : D0 ≠ 0 := by
      intro e
      apply hnd
      rw [← hBe, e, mul_zero, add_zero, hB0]
      exact dvd_mul_right _ _
    have hmdiv : B / u = m := by rw [hm, Ordinal.mul_div_cancel _ hu0]
    have hD0p : D0 < p := by
      have := uc_dig_lt hpSC.1 hBE hcomp γ
      rwa [← hudef, hmdiv] at this
    have hlt' : u * D0 < u2 := by rw [hu2]; exact (mul_lt_mul_iff_right₀ hupos).2 hD0lt
    have hBdiv : B / u2 = m / OmTwo := by
      calc B / u2 = (u2 * (m / OmTwo) + u * D0) / u2 := by rw [← hB0, hBe]
        _ = m / OmTwo := by
          rw [Ordinal.mul_add_div _ (uc_W_pos _).ne', Ordinal.div_eq_zero_of_lt hlt', add_zero]
    have hB0m : B0 ∈ S.CSet B p := by
      have := Ts.ts_mod_mem (S := S) (m := γ + 1) le_add_self B hown
      rwa [uc_leWe, ← hu2def, hBdiv] at this
    have hB0B : B0 < B := by
      rw [← hBe]; exact lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD00))
    have hB0p : S.psi B0 (Om (1 + 1)) < p := psi_lt_psi_of_mem hκ hB0B hB0m
    have hle := ucUB (S := S) hγ B0 (S.psi B0 (Om (1 + 1))) D0
      (by rw [hB0]; exact huu2.trans (dvd_mul_right _ _)) (hB0B.trans hBE) (ucH_le_self _ _) hD0lt.le
    rw [hBe] at hle
    have hlt : S.psi B0 (Om (1 + 1)) + D0 < p := (Lq.lq_SC_indec hpSC).add_lt hB0p hD0p
    have h2 : ucH γ (S.psi B0 (Om (1 + 1)) + D0) < p := by
      conv_rhs => rw [← hfix]
      exact (ucH_lt_iff γ).2 hlt
    exact absurd (hle.trans_lt h2) (lt_irrefl _)

/-! ## The bridge at level `γ` -/

/-- **`ψ(B + Ω₂^γ·D) = H_γ(c + D)`, and `D < ψ(B + Ω₂^γ·D)`**, when `d < H_γ(c + d)` for every `d ≤ D`, for an own
`B < E₂` with `Ω₂^γ ∣ B` and `H_γ(c) = ψ(B)`, `D < Ω₂`, given FWD below `γ < E₂`. -/
theorem uc_eq {γ : Ordinal.{0}} (hγ : γ < ucE) (hF : ∀ j < γ, UcFWD S j)
    {B c : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (1 + 1)))) (hB : OmTwo ^ γ ∣ B) (hBE : B < ucE)
    (hc : ucH γ c = S.psi B (Om (1 + 1))) :
    ∀ D, D < OmTwo → (∀ d, d ≤ D → d < ucH γ (c + d)) →
      D < S.psi (B + OmTwo ^ γ * D) (Om (1 + 1)) ∧ S.psi (B + OmTwo ^ γ * D) (Om (1 + 1)) = ucH γ (c + D) := by
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  set u := OmTwo ^ γ with hudef
  have hupos : 0 < u := uc_W_pos γ
  intro D
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hDΩ hcond
  have hIH : ∀ d, d < D → S.psi (B + u * d) (Om (1 + 1)) = ucH γ (c + d) :=
    fun d hd => (IH d hd (hd.trans hDΩ) fun d' hd' => hcond d' (hd'.trans hd.le)).2
  have heq : S.psi (B + u * D) (Om (1 + 1)) = ucH γ (c + D) := by
    rcases eq_or_ne D 0 with rfl | hD0
    · rw [mul_zero, add_zero, add_zero, hc]
    set v := S.psi (B + u * D) (Om (1 + 1)) with hv
    have hvSC : SC v := Ts.ts_psi_SC _
    have hBv : S.psi B (Om (1 + 1)) < v :=
      Ts.ts_psi_lt_of_own hown (lt_add_of_pos_right _ (mul_pos hupos (pos_iff_ne_zero.2 hD0)))
    have hCv : ucC γ < v := (ucH_C_lt γ c).trans (hc ▸ hBv)
    have hγv : UcLt v γ := (ucC_lt_iff hvSC.1 γ).1 hCv
    have hlt : ∀ d, d < D → ucH γ (c + d) < v := by
      intro d hd
      have hle : S.psi (B + u * d) (Om (1 + 1)) ≤ v :=
        (psi_mono (S := S) hκ ((add_le_add_iff_left B).2 (mul_le_mul_left' hd.le _))).1
      have hdv : d < v := (hcond d hd.le).trans_le (by rw [← hIH d hd]; exact hle)
      have hmem : B + u * d ∈ S.CSet (B + u * D) v :=
        CSet.add_mem ((psi_mono (S := S) hκ (le_self_add : B ≤ B + u * D)).2 hown) (uc_W_mem hγ hγv hdv)
      rw [← hIH d hd]
      exact psi_lt_psi_of_mem hκ ((add_lt_add_iff_left B).2 ((mul_lt_mul_iff_right₀ hupos).2 hd)) hmem
    apply le_antisymm
    · exact ucUB hγ B c D hB hBE hc.ge hDΩ.le
    · rcases zero_or_succ_or_isSuccLimit D with h0 | ⟨d0, rfl⟩ | hlim
      · exact absurd h0 hD0
      · rw [Order.succ_eq_add_one] at hlt hDΩ ⊢
        have hd0v : d0 < v := (hcond d0 (Order.le_succ d0)).trans (hlt d0 (lt_add_one d0))
        have hDv : d0 + 1 < v := hvSC.add_one_lt hd0v
        have hown1 : B + u * (d0 + 1) ∈ S.CSet (B + u * (d0 + 1)) v :=
          CSet.add_mem ((psi_mono (S := S) hκ (le_self_add : B ≤ B + u * (d0 + 1))).2 hown)
            (uc_W_mem hγ hγv hDv)
        have hne : B + u * (d0 + 1) ≠ 0 :=
          (lt_of_lt_of_le (mul_pos hupos (lt_of_le_of_lt zero_le (lt_add_one d0))) le_add_self).ne'
        have hfix : ∀ j < γ, ucC j < v → ucG ucC Om1 j v = v := fun j hj hcj =>
          hF j hj _ hown1 ((opow_dvd_opow _ (Order.add_one_le_of_lt hj)).trans
            (dvd_add hB (dvd_mul_right _ _))) hne hcj
        obtain ⟨e, he⟩ := ucG_range (d := ucC) (L := Om1) hvSC
          (by rw [Rj.rj_Om1]; exact Ts.ts_Om1_lt_psi _) hCv hfix
        have hle' : c + (d0 + 1) ≤ e := by
          refine not_lt.1 fun hlt' => ?_
          have hle : e ≤ c + d0 := by
            rw [← add_assoc] at hlt'; exact Order.lt_add_one_iff.1 hlt'
          have := ((ucG_le_iff (d := ucC) (L := Om1) γ).2 hle).trans_lt (hlt d0 (lt_add_one d0))
          rw [he] at this
          exact lt_irrefl _ this
        calc ucH γ (c + (d0 + 1)) ≤ ucG ucC Om1 γ e := (ucG_le_iff (d := ucC) (L := Om1) γ).2 hle'
          _ = v := he
      · refine not_lt.1 fun hlt' => ?_
        obtain ⟨e, he, hve⟩ := ((ucH_normal γ).lt_iff_exists_lt (isSuccLimit_add c hlim)).1 hlt'
        rcases lt_or_ge e c with hec | hce
        · have : ucH γ e < v := ((ucH_lt_iff γ).2 hec).trans_le (by rw [hc]; exact hBv.le)
          exact absurd hve (not_lt.2 this.le)
        · have hσe : c + (e - c) = e := Ordinal.add_sub_cancel_of_le hce
          have hσ : e - c < D := by rw [← hσe] at he; exact (add_lt_add_iff_left c).1 he
          have := hlt _ hσ
          rw [hσe] at this
          exact absurd hve (not_lt.2 this.le)
  exact ⟨by rw [heq]; exact hcond D le_rfl, heq⟩

/-- **The `ψ_{Ω₂} ↔ H_γ` lemma at every level `γ < E₂`** (FWD discharged). -/
theorem uc_eq_all {γ B c D : Ordinal.{0}} (hγ : γ < ucE) (hown : B ∈ S.CSet B (S.psi B (Om (1 + 1))))
    (hB : OmTwo ^ γ ∣ B) (hBE : B < ucE) (hc : ucH γ c = S.psi B (Om (1 + 1))) (hD : D < OmTwo)
    (hcond : ∀ d, d ≤ D → d < ucH γ (c + d)) :
    D < S.psi (B + OmTwo ^ γ * D) (Om (1 + 1)) ∧ S.psi (B + OmTwo ^ γ * D) (Om (1 + 1)) = ucH γ (c + D) :=
  uc_eq hγ (fun j hj => (uc_fwd_conv j (hj.trans hγ)).1) hown hB hBE hc D hD hcond

/-- **`ψ(Ω₂^γ·(1 + D)) = H_γ(c + D)`** for `γ < E₂` with `ucC γ < ψ(Ω₂^γ) = H_γ(c)`, and a valid `D < Ω₂`. -/
theorem uc_psiU_mul_all {γ c D : Ordinal.{0}} (hγ : γ < ucE) (hC : ucC γ < S.psi (OmTwo ^ γ) (Om (1 + 1)))
    (hc : ucH γ c = S.psi (OmTwo ^ γ) (Om (1 + 1))) (hD : D < OmTwo) (hcond : ∀ d, d ≤ D → d < ucH γ (c + d)) :
    D < S.psi (OmTwo ^ γ * (1 + D)) (Om (1 + 1)) ∧ S.psi (OmTwo ^ γ * (1 + D)) (Om (1 + 1)) = ucH γ (c + D) := by
  have hown : OmTwo ^ γ ∈ S.CSet (OmTwo ^ γ) (S.psi (OmTwo ^ γ) (Om (1 + 1))) := by
    have := uc_W_mem (S := S) (a := OmTwo ^ γ) hγ ((ucC_lt_iff (zero_le.trans_lt hC) γ).1 hC)
      (uc_one_lt_SC (Ts.ts_psi_SC _))
    rwa [mul_one] at this
  have h := uc_eq_all hγ hown dvd_rfl (uc_W_lt_E hγ) hc hD hcond
  rwa [← mul_one (OmTwo ^ γ), mul_assoc, one_mul, ← mul_add] at h

end Googology.Trans.PoR.InaccPsi.R2.Uc
