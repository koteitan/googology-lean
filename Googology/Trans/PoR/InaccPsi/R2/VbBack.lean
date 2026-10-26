import Googology.Trans.PoR.InaccPsi.R2.VbDef

/-!
# The backward transfer of normal arguments, generic in the level

`Θ = gxTh Z At` (codes over a strongly critical `Z < Ω₁` with the atoms `At`), `W = rxW Z At`, `κ = Rx.rxL S Z At W`
the level shift, `RxE S W` its domain, `ψ_k = ψ_{Ω_k}`.

* `vbE_psi` (**`ψ_{k+1}(y)` is a member** for every member `y`, normal or not, `k ≥ 1`);
* `vbNf` (**the normal argument `m ≥ y` of `ψ_{k+1}(y)`**: a member with `ψ_{k+1}(m) = ψ_{k+1}(y)`);
* `vbBack` (**THE BACKWARD TRANSFER**, one statement for every level `k ≥ 1`): if `κ y = d` and `d` is a normal
  argument for `ψ_{k+2}` (`d ∈ Cl(d, ψ_{k+2}(d))`), then `y` is a normal argument for `ψ_{k+1}`
  (`y ∈ Cl(y, ψ_{k+1}(y))`).  Proof: with `P = ψ_{k+1}(y)`, `X = ψ_{k+2}(d)`, `κ P = ψ_{k+2}(κ m) ≥ X`; every member `z`
  with `κ z ∈ Cl(d, X)` lies in `Cl(y, P)` (induction on the measure of `z`: `κ z < X` gives `z < P` by the
  monotonicity of `κ`; otherwise the parts of `z` have their `κ`-values in `Cl(d, X)`, and an atom `ψ_{j+1}(e) ≥ ψ`
  has `κ e < d`, so `e < y`).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

theorem vbNat_lt_omega (k : ℕ) : (k : Ordinal.{0}) + 1 + 1 < ω := by
  have := natCast_lt_omega0 (k + 1 + 1); push_cast at this; exact this

theorem vbOm_lt_W (k : ℕ) : Om ((k : Ordinal.{0}) + 1 + 1) < Om ω := Om_lt_Om.2 (vbNat_lt_omega k)

/-- **`ψ_{k+1}(y)` is a member** for every member `y`. -/
theorem vbE_psi {T y : Ordinal.{0}} {k : ℕ} (hT1 : T ≤ Om 1) (hk : 1 ≤ k) (hy : RxE S T y) :
    RxE S T (S.psi y (Om ((k : Ordinal.{0}) + 1))) := by
  refine ⟨rxN_psi hT1 y hy.1 _ (InR_Om_succ _) (rxNat_ne_one hk) (RxN.om (RxN.succ (rxN_nat k))), ?_, ?_⟩
  · rcases lt_or_ge (S.psi y (Om ((k : Ordinal.{0}) + 1))) (ConjT.th S) with h | h
    · exact CSet.of_lt h
    · exact CSet.psi_mem hy.2.2 (InR_Om_succ _) (rxC_Om_succ _ _ k) hy.2.1
  · refine (psi_lt (InR_Om_succ _) _).trans (Om_lt_Om.2 ?_)
    exact_mod_cast (show ((k + 1 : ℕ) : Ordinal.{0}) < ω from natCast_lt_omega0 _)

/-- **The normal argument `m ≥ y` of `ψ_{k+1}(y)`.** -/
theorem vbNf {T y : Ordinal.{0}} {k : ℕ} (hT1 : T ≤ Om 1) (hk : 1 ≤ k) (hy : RxE S T y) :
    ∃ m, RxE S T m ∧ m ∈ S.CSet m (S.psi m (Om ((k : Ordinal.{0}) + 1))) ∧
      S.psi m (Om ((k : Ordinal.{0}) + 1)) = S.psi y (Om ((k : Ordinal.{0}) + 1)) ∧ y ≤ m ∧
      rxH S T m < rxH S T (S.psi y (Om ((k : Ordinal.{0}) + 1))) := by
  have hP := vbE_psi hT1 hk hy
  have hb := psiS_bounds (S := S) y (k : Ordinal.{0})
  have hS : SC (S.psi y (Om ((k : Ordinal.{0}) + 1))) := SC_psi (InR_Om_succ _) y
  have h1 : Om 1 < S.psi y (Om ((k : Ordinal.{0}) + 1)) := (rxOm1_le_nat hk).trans_lt hb.1
  have hne : ¬ ∃ j : ℕ, S.psi y (Om ((k : Ordinal.{0}) + 1)) = Om (j : Ordinal.{0}) := fun ⟨j, e⟩ =>
    not_Om_of_between hb.1 hb.2 _ e
  obtain ⟨j, -, m, hmE, hmn, hPm, hst⟩ := rxE_atom hT1 hP hS h1 hne
  have hjk : (j : Ordinal.{0}) + 1 = k + 1 := by
    have := sub_eq_of_psi_eq (InR_Om_succ _) (InR_Om_succ _) hPm.symm
    exact Om_inj.1 this
  have hjk' : j = k := by
    have : j + 1 = k + 1 := by exact_mod_cast hjk
    omega
  subst hjk'
  refine ⟨m, hmE, hmn, hPm.symm, ?_, hst⟩
  by_contra hlt
  push Not at hlt
  have hmC : m ∈ S.CSet y (S.psi y (Om ((j : Ordinal.{0}) + 1))) := by
    have := CSet_mono (S := S) hlt.le le_rfl hmn
    rwa [← hPm] at this
  have hPC : S.psi y (Om ((j : Ordinal.{0}) + 1)) ∈ S.CSet y (S.psi y (Om ((j : Ordinal.{0}) + 1))) := by
    have h := CSet.psi_mem (S := S) hlt (InR_Om_succ _) (rxC_Om_succ _ _ j) hmC
    rwa [← hPm] at h
  exact psi_notMem (InR_Om_succ _) y hPC

section Back

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)

include hZ hZ1 hAt

/-- **THE BACKWARD TRANSFER**: `κ y = d` normal for `ψ_{k+2}` makes `y` normal for `ψ_{k+1}` (`k ≥ 1`). -/
theorem vbBack {d y : Ordinal.{0}} {k : ℕ} (hk : 1 ≤ k) (hy : RxE S (rxW Z At) y)
    (hκ : rxL S Z At (rxW Z At) y = d)
    (hdn : d ∈ S.CSet d (S.psi d (Om ((k : Ordinal.{0}) + 1 + 1)))) :
    y ∈ S.CSet y (S.psi y (Om ((k : Ordinal.{0}) + 1))) := by
  have hW1 := rxW_le_Om1 (Z := Z) (At := At)
  set P := S.psi y (Om ((k : Ordinal.{0}) + 1)) with hPdef
  set X := S.psi d (Om ((k : Ordinal.{0}) + 1 + 1)) with hXdef
  obtain ⟨m, hmE, hmn, hPm, hym, -⟩ := vbNf hW1 hk hy
  have hκP : rxL S Z At (rxW Z At) P = S.psi (rxL S Z At (rxW Z At) m) (Om ((k : Ordinal.{0}) + 1 + 1)) := by
    rw [hPdef, ← hPm]; exact (rxL_psiE hk hmE hmn).1
  have hdm : d ≤ rxL S Z At (rxW Z At) m := by
    rcases hym.lt_or_eq with h | h
    · rw [← hκ]; exact (rxL_mono hZ hZ1 hAt hy hmE h).le
    · rw [← hκ, h]
  have hXP : X ≤ rxL S Z At (rxW Z At) P := by rw [hκP]; exact (psi_mono (InR_Om_succ _) hdm).1
  have hPE : RxE S (rxW Z At) P := vbE_psi hW1 hk hy
  have hX2 : Om ((k : Ordinal.{0}) + 1) < X := (psiS_bounds (S := S) d _).1
  have hXL : X ≤ S.Lam := ((psi_lt (InR_Om_succ _) _).trans ((vbOm_lt_W k).trans rxOmW_lt_Lam)).le
  have h2k : Om (1 + 1 : Ordinal.{0}) ≤ Om ((k : Ordinal.{0}) + 1) := by
    have h1k : (1 : Ordinal.{0}) ≤ k := by exact_mod_cast hk
    exact Om_le_Om.2 (by gcongr)
  have claim : ∀ z, RxE S (rxW Z At) z → rxL S Z At (rxW Z At) z ∈ S.CSet d X → z ∈ S.CSet y P := by
    refine rxMs_ind (S := S) (T := rxW Z At) fun z IH hz hzC => ?_
    rcases lt_or_ge (rxL S Z At (rxW Z At) z) X with hzX | hzX
    · apply CSet.of_lt
      by_contra hPz
      push Not at hPz
      rcases hPz.lt_or_eq with h | h
      · exact absurd ((hXP.trans_lt (rxL_mono hZ hZ1 hAt hPE hz h)).trans hzX) (lt_irrefl _)
      · rw [← h] at hzX; exact absurd (hXP.trans_lt hzX) (lt_irrefl _)
    rcases lt_or_ge z (Om 1) with h1 | h1
    · exfalso
      obtain ⟨e, h2, -⟩ := rxL_small hZ hZ1 hAt hz h1
      rw [e] at hzX
      exact absurd (hzX.trans_lt (h2.trans_le h2k)) (not_lt.2 hX2.le)
    by_cases hΩ : ∃ j : ℕ, z = Om (j : Ordinal.{0})
    · obtain ⟨j, rfl⟩ := hΩ; exact rxC_Om_nat _ _ j
    have hz1 : Om 1 < z := lt_of_le_of_ne h1 (fun e => hΩ ⟨1, by rw [← e, Nat.cast_one]⟩)
    by_cases hS : SC z
    · obtain ⟨i, hi, e, heE, hen, rfl, hst⟩ := rxE_atom hW1 hz hS hz1 hΩ
      have hκz := (rxL_psiE hi heE hen).1
      have hκen := rxL_tr hZ hZ1 hAt hi heE heE hen hen
      rw [hκz] at hzC hzX
      obtain ⟨heC, hed⟩ := arg_mem_of_psi_mem (InR_Om_succ _) hzC hzX hXL hκen
      have heP := IH e (rxMs_lt_stage (rxE_lt_Lam heE) hst) heE heC
      have hey : e < y := by
        by_contra hc
        push Not at hc
        rcases hc.lt_or_eq with h | h
        · exact absurd (rxL_mono hZ hZ1 hAt hy heE h) (by rw [hκ]; exact not_lt.2 hed.le)
        · rw [← h, hκ] at hed; exact lt_irrefl _ hed
      exact CSet.psi_mem hey (InR_Om_succ _) (rxC_Om_succ _ _ i) heP
    by_cases hε : ω ^ z = z
    · obtain ⟨hv, -, ha, hb⟩ := rxVeb hz1 hε hS
      obtain ⟨haE, hbE, hha, hhb⟩ := rxE_veb hz hv hb
      have hκz := rxL_veb (Z := Z) (At := At) hz hz1 hε hS
      have hκb := rxL_mono hZ hZ1 hAt hbE hz hb
      obtain ⟨haC, hbC⟩ := rxCDecV hzC _ _ hκz.symm hκb
      have h := CSet.phi_mem (IH _ (rxMs_lt_val hha ha) haE haC) (IH _ (rxMs_lt_val hhb hb) hbE hbC)
      rwa [hv] at h
    · obtain ⟨n, hn1, hdm', hκz, hlE, hrE, hoE, hrlt, hopx, hℓ1, hor, hlh, hrh, -⟩ :=
        rxLDecK hZ hZ1 hAt hz h1
      have hlz : log ω z < z := hor.resolve_left hε
      have hκo := rxL_opow hZ hZ1 hAt hlE hoE hℓ1
      have hκr : rxL S Z At (rxW Z At) (z % ω ^ log ω z) < ω ^ rxL S Z At (rxW Z At) (log ω z) := by
        rw [← hκo]; exact rxL_mono hZ hZ1 hAt hrE hoE hrlt
      have hn0 : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hlogκ : log ω (rxL S Z At (rxW Z At) z) = rxL S Z At (rxW Z At) (log ω z) := by
        rw [hκz, log_opow_mul_add one_lt_omega0 hn0 hκr, log_eq_zero (natCast_lt_omega0 n), add_zero]
      have hlC : rxL S Z At (rxW Z At) (log ω z) ∈ S.CSet d X := by rw [← hlogκ]; exact (rxCDec _ hzC).2
      have hopC : ω ^ rxL S Z At (rxW Z At) (log ω z) ∈ S.CSet d X := by
        have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) hlC; rwa [veblen_zero_apply] at this
      have hoC := ConjT.mul_nat_mem S hopC n
      have hrC : rxL S Z At (rxW Z At) (z % ω ^ log ω z) ∈ S.CSet d X := by
        have h := (rxCDec _ hzC).1 _ hoC (by rw [hκz]; exact le_self_add)
        rwa [hκz, Ordinal.add_sub_cancel] at h
      have hlP := IH _ (rxMs_lt_val hlh hlz) hlE hlC
      have hrP := IH _ (rxMs_lt_val hrh (hrlt.trans_le hopx)) hrE hrC
      have hopP : ω ^ log ω z ∈ S.CSet y P := by
        have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) hlP; rwa [veblen_zero_apply] at this
      have h := CSet.add_mem (ConjT.mul_nat_mem S hopP n) hrP
      rwa [← hdm'] at h
  exact claim y hy (by rw [hκ]; exact hdn)

end Back

end Googology.Trans.PoR.InaccPsi.R2.Vb
