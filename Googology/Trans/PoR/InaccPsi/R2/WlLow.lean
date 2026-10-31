import Googology.Trans.PoR.InaccPsi.R2.RxTh
import Googology.Trans.PoR.InaccPsi.R2.WgTh
import Googology.Trans.PoR.InaccPsi.R2.WgFam

/-!
# The lower half of the reading of `θ`: `ψ_{Ω₁}(A + θ) ≤ Θ_λ(θ)`, hence `Θ_λ(θ) = ψ_{Ω₁}(A + θ)`

`Θ = gxTh ρ_λ (ldAtR λ)`, `θ = ψ_{Ω₂}(Ω_ω)`, `A = A_{η_λ}`, `κ = Rx.rxL` (the level shift `Ω_k ↦ Ω_{k+1}`,
`ψ_{Ω_{k+1}}(d) ↦ ψ_{Ω_{k+2}}(κ d)`), `B_k = ψ_{Ω₂}(Ω_{k+1})`.

The lift of `Rx.rxBlkTh` at the base `0` fails (`Rx.rxL_memH` needs `Ω_ω ≤ a`).  Here the lift is taken at the
base `Ω_{k+2}` for the offsets `ζ < B_k`: every collapse argument inside such a `ζ` is below `Ω_{k+1}`, so its
shift is below `Ω_{k+2}`, which the argument `Ω_{k+2} + κ ζ` dominates.

* `wlL_memB` (**`κ x ∈ Cl(a, b)` for a member `x ∈ Cl(Ω_{k+1}, B_k)` when `Ω_{k+2} ≤ a`**; the level-bounded form
  of `Rx.rxL_memH`);
* `wlCof` (`θ = sup_k B_k`);
* `wlBlk0` (**the block step at the base `0`**: for every `ζ < θ` an atom `t < θ` of `λ` with
  `ψ_{Ω₁}(A + ζ) ≤ Θ_λ(t)`; the atoms are `ψ_{Ω₂}(Ω_{k+2} + κ w)`);
* `wlThLow` (**`Wg.WgThLow` at every restart**), `wlThVal` (**`Θ_λ(θ) = ψ_{Ω₁}(A + θ)`** for every own `A` with
  `ψ_{Ω₁}(A) = ρ_λ`), `wlTh_ups` (**`Θ_λ(θ) = υ_{λ+1}`**), `wlThVal_wit` (non-vacuity at the restart of `m* = L(0)`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wl

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

section K

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)
include hZ hZ1 hAt

/-- **`κ x ∈ Cl(a, b)`** for a member `x ∈ Cl(Ω_{k+1}, ψ_{Ω₂}(Ω_{k+1}))` over `T ≤ W` when `Ω_{k+2} ≤ a` and
every `ruInv g`, `g < T`, is in `Cl(a, b)`. -/
theorem wlL_memB {T a b : Ordinal.{0}} (k : ℕ) (hT : SC T) (hTW : T ≤ rxW Z At)
    (ha : Om ((k : Ordinal.{0}) + 1 + 1) ≤ a)
    (hinv : ∀ g, g < T → ruInv Z At g ∈ S.CSet a b) :
    ∀ x, RxE S T x →
      x ∈ S.CSet (Om ((k : Ordinal.{0}) + 1)) (S.psi (Om ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) →
      rxL S Z At (rxW Z At) x ∈ S.CSet a b := by
  have hW1 := rxW_le_Om1 (Z := Z) (At := At)
  have hT1 : T ≤ Om 1 := hTW.trans hW1
  have hB2 : S.psi (Om ((k : Ordinal.{0}) + 1)) (Om (1 + 1)) < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
  have hBL : S.psi (Om ((k : Ordinal.{0}) + 1)) (Om (1 + 1)) ≤ S.Lam :=
    hB2.le.trans (lt_Lam_of_mem zero_le (Mx.mxOm2_mem (S := S) 0 0)).le
  refine rxMs_ind (S := S) (T := rxW Z At) fun x IH hx hxB => ?_
  have hxW : RxE S (rxW Z At) x := hx.mono hTW
  rcases lt_or_ge x (Om 1) with h1 | h1
  · rw [(rxL_small hZ hZ1 hAt hxW h1).1]; exact hinv x (rxE_lt_T hT hx h1)
  by_cases hΩ : ∃ j : ℕ, x = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    have hj : 1 ≤ j := by
      by_contra h0
      have : j = 0 := by omega
      subst this
      rw [Nat.cast_zero, Om_zero] at h1; exact absurd h1 (not_le.2 (Om_pos one_ne_zero))
    rw [rxL_Om hj]; exact rxC_Om_succ _ _ j
  have h1' : Om 1 < x := lt_of_le_of_ne h1 fun e => hΩ ⟨1, by rw [Nat.cast_one]; exact e.symm⟩
  by_cases hS : SC x
  · obtain ⟨j, hj, d, hdE, hdn, rfl, -⟩ := rxE_atom hT1 hx hS h1' hΩ
    obtain ⟨hK, hdh⟩ := rxL_psiE hj (hdE.mono hTW) hdn
    have hdc : d ∈ S.CSet (Om ((k : Ordinal.{0}) + 1)) (S.psi (Om ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) ∧
        d < Om ((k : Ordinal.{0}) + 1) := by
      rcases le_or_gt (S.psi (Om ((k : Ordinal.{0}) + 1)) (Om (1 + 1)))
          (S.psi d (Om ((j : Ordinal.{0}) + 1))) with hBx | hxB'
      · exact arg_mem_of_psi_mem (InR_Om_succ _) hxB hBx hBL hdn
      · have hj1 : (j : Ordinal.{0}) = 1 := by
          have hb := psiS_bounds (S := S) d (j : Ordinal.{0})
          have h3 : (j : Ordinal.{0}) < 1 + 1 := Om_lt_Om.1 (hb.1.trans (hxB'.trans hB2))
          have : j < 2 := by
            have h4 : (j : Ordinal.{0}) < 2 := by rwa [one_add_one_eq_two] at h3
            exact_mod_cast h4
          have : j = 1 := by omega
          subst this; exact Nat.cast_one
        rw [hj1] at hxB' hdn
        have hdlt : d < Om ((k : Ordinal.{0}) + 1) := by
          by_contra hcon
          push Not at hcon
          exact absurd (psi_mono (S := S) (InR_Om_succ 1) hcon).1 (not_le.2 hxB')
        exact ⟨(psi_mono (S := S) (InR_Om_succ 1) hdlt.le).2 hdn, hdlt⟩
    rw [hK]
    exact CSet.psi_mem ((rxL_lt_lev hZ hZ1 hAt d (hdE.mono hTW) k hdc.2).trans_le ha) (InR_Om_succ _)
      (rxC_Om_succ2 _ _ j) (IH d (rxMs_lt_stage (rxE_lt_Lam hdE) hdh) hdE hdc.1)
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, -, ha', hb⟩ := rxVeb h1' hε hS
    obtain ⟨haE, hbE, -, -⟩ := rxE_veb hx hv hb
    obtain ⟨-, -, hha, hhb⟩ := rxE_veb hxW hv hb
    obtain ⟨haC, hbC⟩ := rxCDecV hxB _ _ hv hb
    rw [rxL_veb hxW h1' hε hS]
    exact CSet.phi_mem (IH _ (rxMs_lt_val hha ha') haE haC) (IH _ (rxMs_lt_val hhb hb) hbE hbC)
  · have hlt := ruLog_lt h1' hε
    have hrlt : x % ω ^ log ω x < x := mod_opow_log_lt_self ω ((Om_pos one_ne_zero).trans h1').ne'
    obtain ⟨hlE, -⟩ := rxE_log hx
    obtain ⟨hrE, -⟩ := rxE_rem hx
    obtain ⟨-, hlh⟩ := rxE_log hxW
    obtain ⟨-, hrh⟩ := rxE_rem hxW
    obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
    have hlC := (rxCDec x hxB).2
    have hrC : x % ω ^ log ω x ∈
        S.CSet (Om ((k : Ordinal.{0}) + 1)) (S.psi (Om ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) := by
      have hdm : x = ω ^ log ω x * n + x % ω ^ log ω x := by
        rw [← hn]; exact (Ordinal.div_add_mod x _).symm
      have e : x - ω ^ log ω x * n = x % ω ^ log ω x := by
        have e0 := Ordinal.add_sub_cancel (ω ^ log ω x * n) (x % ω ^ log ω x)
        rwa [← hdm] at e0
      have hle : ω ^ log ω x * n ≤ x := le_self_add.trans_eq hdm.symm
      have hop : ω ^ log ω x ∈
          S.CSet (Om ((k : Ordinal.{0}) + 1)) (S.psi (Om ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) := by
        have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) hlC; rwa [veblen_zero_apply] at this
      have hC := (rxCDec x hxB).1 _ (ConjT.mul_nat_mem S hop n) hle
      rwa [e] at hC
    rw [rxL_gt hxW h1' hlt, hn]
    have h1m := IH _ (rxMs_lt_val hlh hlt) hlE hlC
    have h2m := IH _ (rxMs_lt_val hrh hrlt) hrE hrC
    have hop : ω ^ rxL S Z At (rxW Z At) (log ω x) ∈ S.CSet a b := by
      have := CSet.phi_mem (S := S) (CSet.zero_mem a b) h1m; rwa [veblen_zero_apply] at this
    exact CSet.add_mem (ConjT.mul_nat_mem S hop n) h2m

end K

/-- **`θ = sup_k ψ_{Ω₂}(Ω_{k+1})`**: every `w < θ` is below some `ψ_{Ω₂}(Ω_{k+1})`. -/
theorem wlCof {w : Ordinal.{0}} (hw : w < ConjT.th S) :
    ∃ k : ℕ, w < S.psi (Om ((k : Ordinal.{0}) + 1)) (Om (1 + 1)) := by
  have hlim : IsSuccLimit (Om ω : Ordinal.{0}) := (SC_Om omega0_ne_zero).isSuccLimit
  have e := Lw.lw_psi_limit S (InR_Om_succ 1) hlim
  have hw' : w < ⨆ e : Iio (Om ω : Ordinal.{0}), S.psi e.1 (Om (1 + 1)) := by
    rw [← e]; exact hw
  have hbdd : BddAbove (range fun e : Iio (Om ω : Ordinal.{0}) => S.psi e.1 (Om (1 + 1))) :=
    ⟨Om (1 + 1), by rintro _ ⟨e, rfl⟩; exact (psi_lt (InR_Om_succ 1) _).le⟩
  haveI : Nonempty (Iio (Om ω : Ordinal.{0})) := ⟨⟨0, Om_pos omega0_ne_zero⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff hbdd).1 hw'
  obtain ⟨n, hn⟩ := rxOmW_nat e.2
  exact ⟨n, he.trans_le (psi_mono (S := S) (InR_Om_succ 1) (hn.le.trans (Om_le_Om.2 le_self_add))).1⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
include hl hX

/-- **THE BLOCK STEP AT THE BASE `0`**: for every `ζ < θ` there is an atom `t < θ` of `λ` with
`ψ_{Ω₁}(A_{η_λ} + ζ) ≤ Θ_λ(t)`. -/
theorem wlBlk0 : ∀ ζ, ζ < ConjT.th S → ∃ t ∈ ldAtR S l, t < ConjT.th S ∧
    S.psi (ConjT.Aη S (cdEta S l) + ζ) (Om 1) ≤ gxTh (upsilon l) (ldAtR S l) t := by
  obtain ⟨hZ, hZ1⟩ := Le.leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hpv : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l := cdEta_pv hl.1 hX
  set A := ConjT.Aη S (cdEta S l) with hAdef
  set W := rxW (upsilon l) (ldAtR S l) with hWdef
  set κ := rxL S (upsilon l) (ldAtR S l) W with hκdef
  have hW : SC W := rxW_SC hZ hZ1 hAt
  have hθSC := ConjT.SC_th S
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
  have hθW : ConjT.th S < Om ω := hθ2.trans (Om_lt_Om.2 (by
    rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2))
  have hWA : Om ω ≤ A := le_self_add
  have hdvd : ConjT.th S ∣ A := by
    have := rxDvdTh (S := S) (cdEta S l) 0; rwa [mul_zero, add_zero] at this
  have hEθ : ∀ {T ζ : Ordinal.{0}}, RxN S T ζ → ζ < ConjT.th S → RxE S T ζ :=
    fun hN hζ => ⟨hN, CSet.of_lt hζ, hζ.trans hθW⟩
  have hκH : ∀ ζ, RxE S W ζ → κ ζ ∈ S.CSet A (upsilon l) :=
    fun ζ hζ => rxL_memH hZ hZ1 hAt hW le_rfl hWA (fun g hg => by
      obtain ⟨hcode, hlt2, -⟩ := ruInv_spec (hg.trans_le (min_le_left _ _))
      exact (ldHull_iff hl hX hlt2).2 hcode) ζ hζ
  have hκ3 : ∀ ζ, RxE S W ζ → ζ < ConjT.th S → κ ζ < Om (1 + 1 + 1) := fun ζ hζ hζθ => by
    have h := rxL_lt_lev hZ hZ1 hAt ζ hζ 1 (by rw [Nat.cast_one]; exact hζθ.trans hθ2)
    rwa [Nat.cast_one] at h
  intro ζ hζθ
  obtain ⟨w, hw, hn, hwθ⟩ := rxCofTh hζθ
  obtain ⟨k, hk⟩ := wlCof hwθ
  have hBθ : S.psi (Om ((k : Ordinal.{0}) + 1)) (Om (1 + 1)) < ConjT.th S :=
    psi_lt_psi_of_mem (InR_Om_succ 1) (Om_lt_Om.2 (by
      have h := natCast_lt_omega0 (k + 1); push_cast at h; exact h)) (rxC_Om_succ _ _ k)
  have hβW : Om ((k : Ordinal.{0}) + 1 + 1 + 1) < Om ω := Om_lt_Om.2 (by
    have h := natCast_lt_omega0 (k + 1 + 1 + 1); push_cast at h; exact h)
  have h3β : Om (1 + 1 + 1 : Ordinal.{0}) ≤ Om ((k : Ordinal.{0}) + 1 + 1 + 1) :=
    Om_le_Om.2 (add_le_add (add_le_add (le_add_self : (1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1) le_rfl) le_rfl)
  have hββ : Om ((k : Ordinal.{0}) + 1 + 1) < Om ((k : Ordinal.{0}) + 1 + 1 + 1) := Om_lt_Om.2 (lt_add_one _)
  have hβκ : ∀ ζ, RxE S W ζ → ζ < ConjT.th S →
      Om ((k : Ordinal.{0}) + 1 + 1) + κ ζ < Om ((k : Ordinal.{0}) + 1 + 1 + 1) := fun ζ hζ hζθ =>
    (SC_Om (by exact (add_pos_of_nonneg_of_pos zero_le zero_lt_one).ne')).isPrincipal hββ
      ((hκ3 ζ hζ hζθ).trans_le h3β)
  have hat : ∀ ζ, RxE S W ζ → ζ < ConjT.th S →
      S.psi (Om ((k : Ordinal.{0}) + 1 + 1) + κ ζ) (Om (1 + 1)) ∈ ldAtR S l :=
    fun ζ hζ hζθ => ⟨_, CSet.add_mem (rxC_Om_succ2 _ _ k) (hκH ζ hζ),
      ((hβκ ζ hζ hζθ).trans hβW).trans_le hWA, rfl⟩
  have hβat : S.psi (Om ((k : Ordinal.{0}) + 1 + 1)) (Om (1 + 1)) ∈ ldAtR S l :=
    ⟨_, rxC_Om_succ2 _ _ k, (hββ.trans hβW).trans_le hWA, rfl⟩
  have hbase : S.psi A (Om 1) ≤
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om ((k : Ordinal.{0}) + 1 + 1)) (Om (1 + 1))) := by
    rw [hpv]
    exact (gxTh_Om1 hZ hZ1 hAt).symm.le.trans (gxTh_mono (psiS_bounds (S := S) _ 1).1.le)
  have hpos : ∀ ζ, RxE S W ζ → ζ ≠ 0 → S.psi (Om ((k : Ordinal.{0}) + 1 + 1)) (Om (1 + 1)) <
      S.psi (Om ((k : Ordinal.{0}) + 1 + 1) + κ ζ) (Om (1 + 1)) := fun ζ hζ h0 =>
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right _ (rxL_pos hZ hZ1 hAt hζ h0))
      (rxC_Om_succ2 _ _ k)
  have hcl : ∀ ζ, RxE S W ζ ∧ ζ < S.psi (Om ((k : Ordinal.{0}) + 1)) (Om (1 + 1)) →
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om ((k : Ordinal.{0}) + 1 + 1) + κ ζ) (Om (1 + 1))) < Om 1 →
      ∀ e, HCl S (A + ζ)
        (gxTh (upsilon l) (ldAtR S l) (S.psi (Om ((k : Ordinal.{0}) + 1 + 1) + κ ζ) (Om (1 + 1)))) e →
      A ≤ e → e < A + ζ →
      (RxE S W (e - A) ∧ e - A < S.psi (Om ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) ∧
        Om ((k : Ordinal.{0}) + 1 + 1) + κ (e - A) ∈
          S.CSet (Om ((k : Ordinal.{0}) + 1 + 1) + κ ζ)
            (S.psi (Om ((k : Ordinal.{0}) + 1 + 1) + κ ζ) (Om (1 + 1))) := by
    intro ζ hζ hcnt e he h1 h2
    set t := S.psi (Om ((k : Ordinal.{0}) + 1 + 1) + κ ζ) (Om (1 + 1)) with htdef
    set Tt := gxTh (upsilon l) (ldAtR S l) t with hTtdef
    have htSC : SC Tt :=
      gxTh_SC hZ hAt (SC_psi (InR_Om_succ 1) _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
    have hTZ : Tt ≤ gxTh (upsilon l) (ldAtR S l) (Om (1 + 1)) := gxTh_mono (psi_lt (InR_Om_succ 1) _).le
    have hTW : Tt ≤ W := le_min hTZ hcnt.le
    have hlt : e - A < ζ := Ry.rySub_lt h1 h2
    have hltB := hlt.trans hζ.2
    have hltθ : e - A < ConjT.th S := hltB.trans hBθ
    have hm : e % ConjT.th S = e - A := by
      have e1 : e = A + (e - A) := (Ordinal.add_sub_cancel_of_le h1).symm
      conv_lhs => rw [e1]
      rw [ldModK_add_lt hθSC A hltθ, Ordinal.mod_eq_zero_of_dvd hdvd, zero_add]
    have hN : RxN S Tt (e - A) := by
      rw [← hm]; exact rxN_of_HCl hcnt.le (ruHCl_modK hθSC he)
    have hET : RxE S Tt (e - A) := hEθ hN hltθ
    refine ⟨⟨hET.mono hTW, hltB⟩, CSet.add_mem (rxC_Om_succ2 _ _ k) ?_⟩
    exact wlL_memB hZ hZ1 hAt k htSC hTW le_self_add
      (fun g hg' => CSet.of_lt (ruInv_spec hg').2.1) _ hET (CSet.of_lt hltB)
  have hLift := rxLift hZ hZ1 hAt hβat hbase
    (D := {ζ | RxE S W ζ ∧ ζ < S.psi (Om ((k : Ordinal.{0}) + 1)) (Om (1 + 1))})
    (fun ζ hζ ζ' hζ' h => rxL_mono hZ hZ1 hAt hζ'.1 hζ.1 h)
    (fun ζ hζ => hat ζ hζ.1 (hζ.2.trans hBθ)) (fun ζ hζ h0 => hpos ζ hζ.1 h0) hcl
  have hwD : RxE S W w := hEθ (hw.mono (ruTwo_le hW)) hwθ
  refine ⟨_, hat w hwD hwθ, ?_, ?_⟩
  · have hβn : Om ((k : Ordinal.{0}) + 1 + 1 + 1) ∈ S.CSet (Om ω) (ConjT.th S) :=
      CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (CSet.succ_mem (rxC_nat _ _ k))))
    exact ((psi_mono (S := S) (InR_Om_succ 1) (hβκ w hwD hwθ).le).1).trans_lt
      (psi_lt_psi_of_mem (InR_Om_succ 1) hβW hβn)
  · exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left A).2 hn)).1.trans (hLift w ⟨hwD, hk⟩)

/-- **The lower half `Wg.WgThLow` at every restart**: `ψ_{Ω₁}(A_{η_λ} + θ) ≤ Θ_λ(θ)`. -/
theorem wlThLow : Wg.WgThLow S l :=
  Wg.wgLow_of_all fun ζ hζ => by
    obtain ⟨t, ht, htθ, hle⟩ := wlBlk0 hl hX ζ hζ
    exact hle.trans_lt (gxTh_lt (GxCl.atom ht) htθ)

/-- **`Θ_λ(θ) = ψ_{Ω₁}(A + θ)`** for every own `A` with `ψ_{Ω₁}(A) = ρ_λ`. -/
theorem wlThVal {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (ConjT.th S) = S.psi (A + ConjT.th S) (Om 1) :=
  Wg.wgThVal_of_low hl hX hA hρ (wlThLow hl hX)

/-- **`Θ_λ(θ) = υ_{λ+1}`** (with `Rx`/`Mx.mxUps_succ`: `υ_{λ+1} = ψ_{Ω₁}(A_{η_λ} + θ)`). -/
theorem wlTh_ups {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (ConjT.th S) = upsilon (l + 1) := by
  rw [wlThVal hl hX hA hρ, mxUps_succ hl hX, (Wg.wgOwnEta hl hX hA hρ).2]

end Main

/-- **Non-vacuity at the witness restart** (`m* = L(0)`, the witness of `SkRX.skrxTopDynAll_false`): a restart with
an own `A`, `ψ_{Ω₁}(A) = ρ_λ`, where `Θ_λ(θ) = ψ_{Ω₁}(A + θ) = υ_{λ+1}`. -/
theorem wlThVal_wit (S : InaccSeq.{0}) :
    ∃ l A : Ordinal.{0}, IsRestartIdx l ∧ upsilon l = Nc.ncL S 0 ∧ A ∈ S.CSet A (S.psi A (Om 1)) ∧
      S.psi A (Om 1) = upsilon l ∧
      gxTh (upsilon l) (ldAtR S l) (ConjT.th S) = S.psi (A + ConjT.th S) (Om 1) ∧
      gxTh (upsilon l) (ldAtR S l) (ConjT.th S) = upsilon (l + 1) := by
  obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
  have hX : upsilon l < Pv S (Om ω + Nc.ncPp S * 1) := by
    rw [← e, ← Lw.lw_L_eq]; exact Rl.rlM_lt_L1
  have hL1 : Nc.ncL S 1 = Bc.bcC S 0 := by simp [Bc.bcC]
  have hn : upsilon l < Bc.bcC S (0 + 1) := by
    rw [← e]
    exact (Rl.rlM_lt_L1 (S := S)).trans_le (hL1 ▸ Bc.bcC_mono (S := S) (Nat.zero_le _))
  obtain ⟨hA, hρ⟩ := Vq.vqA_spec hl hX (n := 0) hn
  exact ⟨l, _, hl, e.symm, hA, hρ, wlThVal hl hX hA hρ, wlTh_ups hl hX hA hρ⟩

end Googology.Trans.PoR.InaccPsi.R2.Wl

#print axioms Googology.Trans.PoR.InaccPsi.R2.Wl.wlL_memB
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wl.wlCof
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wl.wlBlk0
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wl.wlThLow
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wl.wlThVal
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wl.wlTh_ups
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wl.wlThVal_wit
