import Googology.Trans.PoR.InaccPsi.R2.XiIt

/-!
# THE IMAGE LAW AT EVERY LEVEL `k` FOR EVERY BASE `β` IN THE DOMAIN OF `T`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Vb.vbT S λ`, `D = Vb.VbD S λ`, `A = A_{η_λ}` (own, `ψ₁(A) = ρ_λ`),
`X̂⁰_k(β) = ψ₂(T β + Ω_{k+2})` (`Wv.wvX0`), `K_j = Ω_{j+3}`.

For `β ∈ D` with `Ro.RoBaseE λ Ω_{k+3} 0 β`:
* upper half: `Xd.xdUp_at` at `a = β + Ω_{k+3}` (`T(β + Ω_{k+3}) = T β + Ω_{k+2}`);
* lower half (`xiLow`, one induction on `k`): `k = 0` is `Xd.xdLow0`; for `k + 1` take the iterates
  `u_0 = 0`, `u_{n+1} = ψ_{Ω_{k+4}}(β + u_n)` (`Xi.xiZ`); every `β + u_n` is a base of `Ω_{k+3}` in `D`
  (`xiBase_u`), `T u_n = z_n` with `z_{n+1} = ψ_{Ω_{k+3}}(T β + z_n)` (`xiT_u`), and
  `ψ₂(T β + Ω_{k+3}) ≤ sup_n ψ₂(T β + z_n)` (`Xi.xiCof`, needs `Ω_{k+3} ∣ T β`: `xiT_mod`); the law at `k`
  on the bases `β + u_n` gives `ψ₁(A + ψ₂(T β + z_n + Ω_{k+2})) ≤ Θ(ψ₂(β + u_n + Ω_{k+3})) ≤ Θ(ψ₂(β + Ω_{k+4}))`.

* `xiT_mod` (`Ω_{k+2} ∣ x ⇒ Ω_{k+1} ∣ T x` on `D`, `k ≥ 1`), `xiLowStep`, `xiLow` (**the lower half**),
  `xiLaw_of_low`, `xiLawDK` (**THE LAW `skX0LawDK`: every `k`, every `β ∈ D`**), `xiBase_Om`, `xiBase_zero`,
  `xiLaw_1_Om4` (`k = 1`, `β = Ω₄`), `xiLaw_2_0` (`k = 2`, `β = 0`), `xiLawDK_wit` (non-vacuity).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vk Googology.Trans.PoR.InaccPsi.R2.Vb

variable {S : InaccSeq.{0}}

theorem xiC2 (k : ℕ) : ((k + 1 + 1 : ℕ) : Ordinal.{0}) = (k : Ordinal.{0}) + 1 + 1 := by
  simp only [Nat.cast_add, Nat.cast_one]

theorem xiOmK_mem (k : ℕ) (a c : Ordinal.{0}) : Om ((k : Ordinal.{0}) + 1 + 1 + 1 + 1) ∈ S.CSet a c := by
  have h := Vn.vnOmK3_mem (S := S) (k + 1) a c; rwa [Nat.cast_succ] at h

theorem xiOmK_lt_W (k : ℕ) : Om ((k : Ordinal.{0}) + 1 + 1 + 1 + 1) < Om ω := by
  have h := Wv.wvOmK_lt_W (k + 1); rwa [Nat.cast_succ] at h

theorem xiPsi2_le4 (k : ℕ) (x X : Ordinal.{0}) :
    S.psi x (Om (1 + 1)) ≤ S.psi X (Om ((k : Ordinal.{0}) + 1 + 1 + 1 + 1)) := by
  have h := Vn.vnPsi2_le_psi (S := S) (k + 1) x X; rwa [Nat.cast_succ] at h

theorem xiWe4 (k : ℕ) :
    Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1 + 1)) = Om ((k : Ordinal.{0}) + 1 + 1 + 1 + 1) := by
  have h := Vn.vnWe_OmK (k + 1); rwa [Nat.cast_succ] at h

theorem xiK34 (k : ℕ) : Om ((k : Ordinal.{0}) + 1 + 1 + 1) < Om ((k : Ordinal.{0}) + 1 + 1 + 1 + 1) :=
  Om_lt_Om.2 (lt_add_one _)

theorem xiNe (k : ℕ) (j : Ordinal.{0}) : (k : Ordinal.{0}) + j + 1 ≠ 0 := (add_pos_of_right zero_lt_one _).ne'

theorem xiHs (k : ℕ) : (k : Ordinal.{0}) + 1 + 1 + 1 < Om 1 :=
  (vkNat_lt_omega k).trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)

theorem xiHs2 (k : ℕ) : Om (1 + 1 : Ordinal.{0}) ≤ Om ((k : Ordinal.{0}) + 1 + 1) := by
  have hk2 : (1 + 1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 + 1 := by gcongr; exact le_add_self
  exact Om_le_Om.2 hk2

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`Ω_{k+2} ∣ x ⇒ Ω_{k+1} ∣ T x`** on the domain (`k ≥ 1`). -/
theorem xiT_mod (k : ℕ) (hk : 1 ≤ k) : ∀ x, VbD S l x → x % Om ((k : Ordinal.{0}) + 1 + 1) = 0 →
    vbT S l x % Om ((k : Ordinal.{0}) + 1) = 0 := by
  have hPS : SC (Om ((k : Ordinal.{0}) + 1 + 1)) := SC_Om (add_pos_of_right zero_lt_one _).ne'
  have hPε := gg_SC_eps hPS
  have hQS : SC (Om ((k : Ordinal.{0}) + 1)) := SC_Om (add_pos_of_right zero_lt_one _).ne'
  have hQε := gg_SC_eps hQS
  have h1k : (1 : Ordinal.{0}) < (k : Ordinal.{0}) + 1 + 1 :=
    lt_of_lt_of_le (lt_add_one 1) (by gcongr; exact le_add_self)
  have h2k : (1 + 1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 + 1 := by gcongr; exact le_add_self
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hm
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Vh.vhT_zero hl hX, Ordinal.zero_mod]
  have hxP : Om ((k : Ordinal.{0}) + 1 + 1) ≤ x := by
    by_contra hc
    push Not at hc
    rw [Ordinal.mod_eq_of_lt hc] at hm
    exact hx0 hm
  have hx2 : Om (1 + 1) ≤ x := (Om_le_Om.2 h2k).trans hxP
  have hTQ : Om ((k : Ordinal.{0}) + 1) ≤ vbT S l x := vbT_ge_lev hl hX hx k hxP
  by_cases hε : ω ^ x = x
  · have he := vbT_eps hl hX hx hx2 hε
    rw [← he] at hTQ ⊢
    exact xiMod_opow hQε hTQ
  have hlog : log ω x < x := ruLog_lt ((Om_lt_Om.2 h1k).trans_le hxP) hε
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hpos : (0 : Ordinal.{0}) < n := hn ▸ div_opow_log_pos ω hx0
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact lt_irrefl _ hpos)
  have hdm : x = ω ^ log ω x * n + x % ω ^ log ω x := by
    rw [← hn]; exact (Ordinal.div_add_mod x _).symm
  have hs : x % ω ^ log ω x < ω ^ log ω x := Ordinal.mod_lt x (opow_pos _ omega0_pos).ne'
  have hsx : x % ω ^ log ω x < x := hs.trans_le (opow_log_le_self ω hx0)
  have hxE := vbD_E hl hX hx
  obtain ⟨heD, -, -⟩ := vbD_log hx hxE
  obtain ⟨hsD, -, -⟩ := vbD_rem hx hxE
  have heP : Om ((k : Ordinal.{0}) + 1 + 1) ≤ log ω x := le_log_of_opow_le one_lt_omega0 (by rw [hPε]; exact hxP)
  have e1 : (ω ^ log ω x * n + x % ω ^ log ω x) % Om ((k : Ordinal.{0}) + 1 + 1) =
      (x % ω ^ log ω x) % Om ((k : Ordinal.{0}) + 1 + 1) := Xd.xdModHead hPε heP n
  rw [← hdm, hm] at e1
  have hTs := IH _ hsx hsD e1.symm
  have hTe : Om ((k : Ordinal.{0}) + 1) ≤ vbT S l (log ω x) := vbT_ge_lev hl hX heD k heP
  rw [(congrArg (vbT S l) hdm).trans (Vh.vhT_cnf hl hX n hn1 heD hsD hs), Xd.xdModHead hQε hTe n]
  exact hTs

/-- **THE STEP `k → k + 1` OF THE LOWER HALF.** -/
theorem xiLowStep {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (k : ℕ)
    (IH : ∀ β, VbD S l β → Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 β →
      S.psi (A + S.psi (vbT S l β + Om ((k : Ordinal.{0}) + 1 + 1)) (Om (1 + 1))) (Om 1) ≤
        gxTh (upsilon l) (ldAtR S l) (S.psi (β + Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1))))
    (β : Ordinal.{0}) (hβD : VbD S l β) (hB : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1 + 1)) 0 β) :
    S.psi (A + S.psi (vbT S l β + Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1))) (Om 1) ≤
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + Om ((k : Ordinal.{0}) + 1 + 1 + 1 + 1)) (Om (1 + 1))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set K4 := Om ((k : Ordinal.{0}) + 1 + 1 + 1 + 1) with hK4
  set K3 := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hK3
  set K2 := Om ((k : Ordinal.{0}) + 1 + 1) with hK2
  have hκ4 : S.InR K4 := InR_Om_succ _
  have hK4S : SC K4 := SC_Om (add_pos_of_right zero_lt_one _).ne'
  have hK3S : SC K3 := SC_Om (add_pos_of_right zero_lt_one _).ne'
  have hK3ε : ω ^ K3 = K3 := gg_SC_eps hK3S
  have hW4 : Le.leWe (K4 + 0) = K4 := by rw [add_zero]; exact xiWe4 k
  have hW3 : Le.leWe (K3 + 0) = K3 := by rw [add_zero]; exact Vn.vnWe_OmK k
  have hAω : Om ω ≤ ConjT.Aη S (cdEta S l) := ConjT.OmW_le_A S _
  obtain ⟨hdvd4, -, hlt4, hnorm4, -⟩ := hB
  rw [hW4] at hdvd4 hlt4 hnorm4
  have hβn2 : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by have h := hnorm4 0 zero_le; rwa [add_zero] at h
  have hβn4 : β ∈ S.CSet β (S.psi β K4) := CSet_mono le_rfl (xiPsi2_le4 k β β) hβn2
  set u := xiZ S K4 β with hu
  have hu_lt : ∀ n, u n < K4 := fun n => xiZ_lt_K n
  have hu_mem : ∀ n a c, β ∈ S.CSet a c → β + u n ≤ a → u n ∈ S.CSet a c :=
    xiZ_mem hβn4 (xiOmK_mem k)
  have hβuK : ∀ n, β + u n < β + K4 := fun n => (add_lt_add_iff_left β).2 (hu_lt n)
  have hβuA : ∀ n, β + u n ≤ ConjT.Aη S (cdEta S l) := fun n => ((hβuK n).trans hlt4).le
  have hβuW : ∀ n, β + u n < Om ω := fun n => vkOmW.1.isPrincipal hβD.2.2 ((hu_lt n).trans (xiOmK_lt_W k))
  have hu_D : ∀ n, VbD S l (u n) := fun n =>
    ⟨hu_mem n _ _ hβD.1 (hβuA n), hu_mem n _ _ hβD.2.1 (hβuW n).le, (hu_lt n).trans (xiOmK_lt_W k)⟩
  have hβu_D : ∀ n, VbD S l (β + u n) := fun n =>
    ⟨CSet.add_mem hβD.1 (hu_D n).1, CSet.add_mem hβD.2.1 (hu_D n).2.1, hβuW n⟩
  -- the image of the base
  set b := vbT S l β with hbdef
  have hbn2 : b ∈ S.CSet b (S.psi b (Om (1 + 1))) := Xd.xdTr hl hX hβD hβD hβn2
  have hbn3 : b ∈ S.CSet b (S.psi b K3) := CSet_mono le_rfl (Vn.vnPsi2_le_psi k b b) hbn2
  have hbm3 : b % K3 = 0 := by
    have h := xiT_mod hl hX (k + 1 + 1) (by omega) β hβD (by
      rw [xiC2]; exact Ordinal.mod_eq_zero_of_dvd hdvd4)
    rwa [xiC2] at h
  set z := xiZ S K3 b with hz
  -- `T u_n = z_n`
  have hnormu : ∀ n, β + u n ∈ S.CSet (β + u n) (S.psi (β + u n) K4) := fun n => by
    have hb' : β ∈ S.CSet (β + u n) (S.psi (β + u n) K4) := (psi_mono hκ4 le_self_add).2 hβn4
    exact CSet.add_mem hb' (hu_mem n _ _ hb' le_rfl)
  have hTu : ∀ n, vbT S l (u n) = z n := by
    intro n
    induction n with
    | zero => exact Vh.vhT_zero hl hX
    | succ n ih =>
      have hdn : β + u n ∈ S.CSet (β + u n)
          (S.psi (β + u n) (Om (((k + 1 + 1 : ℕ) : Ordinal.{0}) + 1 + 1))) := by
        rw [xiC2]; exact hnormu n
      have h := (vbT_atom hl hX (k := k + 1 + 1) (by omega) (hβu_D n) hdn).1
      rw [xiC2] at h
      change vbT S l (S.psi (β + u n) K4) = S.psi (b + z n) K3
      rw [h, Vh.vhT_add hl hX hβD (hu_D n), ih]
  -- every `β + u_n` is a base of `Ω_{k+3}`
  have hK3K4 : K3 ∣ K4 := Ordinal.dvd_iff_mod_eq_zero.2 (Xd.xdModG hK3ε hK4S (xiK34 k).le)
  have hu_dvd : ∀ n, K3 ∣ u n := by
    intro n
    cases n with
    | zero => exact dvd_zero _
    | succ n =>
      refine Ordinal.dvd_iff_mod_eq_zero.2 (Xd.xdModG hK3ε (xiZ_SC n) ?_)
      change K3 ≤ S.psi (β + u n) K4
      exact (psiS_bounds (S := S) _ _).1.le
  have huK : ∀ n, u n + K3 < K4 := fun n => hK4S.isPrincipal (hu_lt n) (xiK34 k)
  have hBu : ∀ n, Ro.RoBaseE S l K3 0 (β + u n) := by
    intro n
    refine ⟨?_, (hβu_D n).1, ?_, ?_, ?_⟩
    · rw [hW3]; exact dvd_add (dvd_trans hK3K4 hdvd4) (hu_dvd n)
    · rw [hW3, add_assoc]
      exact ((add_lt_add_iff_left β).2 (huK n)).trans hlt4
    · intro d hd
      rw [hW3] at hd
      have hd4 : u n + d ≤ K4 := ((add_le_add le_rfl hd).trans_lt (huK n)).le
      have hb' : β ∈ S.CSet (β + u n + d) (S.psi (β + u n + d) (Om (1 + 1))) := by
        rw [add_assoc]; exact hnorm4 _ hd4
      exact CSet.add_mem hb' (hu_mem n _ _ hb' le_self_add)
    · intro e' _ he'
      rw [nonpos_iff_eq_zero.1 he']
      exact (Om_pos one_ne_zero).trans (psiS_bounds (S := S) _ 1).1
  -- the lower half
  set Xh := S.psi (b + K3) (Om (1 + 1)) with hXhdef
  have hXSC : SC Xh := SC_psi hκ2 _
  have hbig : ∀ ζ, ζ < Xh → S.psi (A + ζ) (Om 1) ≤
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + K4) (Om (1 + 1))) := by
    intro ζ hζ
    obtain ⟨n, hn⟩ := xiCof_lt (s := (k : Ordinal.{0}) + 1 + 1) hbn3 (xiHs k) (xiHs2 k) hbm3 hζ
    have h1 := IH (β + u n) (hβu_D n) (hBu n)
    rw [Vh.vhT_add hl hX hβD (hu_D n), hTu n] at h1
    have hle : β + u n + K3 ≤ β + K4 := by rw [add_assoc]; exact add_le_add le_rfl (huK n).le
    have h2 := gxTh_mono (Z := upsilon l) (At := ldAtR S l) (psi_mono hκ2 hle).1
    have h0 : ζ ≤ S.psi (b + z n + K2) (Om (1 + 1)) := hn.le.trans (psi_mono hκ2 le_self_add).1
    exact ((psi_mono (S := S) Low.InR_Om_one (add_le_add le_rfl h0)).1.trans h1).trans h2
  have hlim : IsSuccLimit (A + Xh) := isSuccLimit_add _ hXSC.isSuccLimit
  rw [Lw.lw_psi_limit S Low.InR_Om_one hlim]
  refine ciSup_le' fun e => ?_
  rcases lt_or_ge e.1 A with h1 | h1
  · have h0 := hbig 0 hXSC.1
    rw [add_zero] at h0
    exact (psi_mono (S := S) Low.InR_Om_one h1.le).1.trans h0
  · have e1 : e.1 = A + (e.1 - A) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt' : e.1 - A < Xh := by
      have h2 := e.2
      change e.1 < A + Xh at h2
      rw [e1] at h2
      exact (add_lt_add_iff_left _).1 h2
    rw [e1]
    exact hbig _ hlt'

/-- **THE LOWER HALF AT EVERY LEVEL `k`, EVERY BASE `β ∈ D`**:
`ψ₁(A + ψ₂(T β + Ω_{k+2})) ≤ Θ(ψ₂(β + Ω_{k+3}))`. -/
theorem xiLow {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    ∀ (k : ℕ) (β : Ordinal.{0}), VbD S l β → Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 β →
      S.psi (A + S.psi (vbT S l β + Om ((k : Ordinal.{0}) + 1 + 1)) (Om (1 + 1))) (Om 1) ≤
        gxTh (upsilon l) (ldAtR S l) (S.psi (β + Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1))) := by
  intro k
  induction k with
  | zero =>
    intro β hβD hB
    simp only [Nat.cast_zero, zero_add] at hB ⊢
    exact Xd.xdLow0 hl hX hA hρ hβD hB
  | succ k IH =>
    intro β hβD hB
    rw [Nat.cast_succ] at hB ⊢
    exact xiLowStep hl hX hA hρ k IH β hβD hB

/-- **The law from its lower half** (the upper half is `Xd.xdUp_at`). -/
theorem xiLaw_of_low {A β : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (k : ℕ) (hβD : VbD S l β) (hB : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 β)
    (hlow : S.psi (A + S.psi (vbT S l β + Om ((k : Ordinal.{0}) + 1 + 1)) (Om (1 + 1))) (Om 1) ≤
        gxTh (upsilon l) (ldAtR S l) (S.psi (β + Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1)))) :
    Wg.WgTopAt S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Wv.wvX0 S l k β) 0 β := by
  obtain ⟨-, rfl⟩ := Wg.wgOwnEta hl hX hA hρ
  obtain ⟨hZ, hZ1⟩ := Le.leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set A := ConjT.Aη S (cdEta S l) with hAdef
  set b := vbT S l β with hbdef
  set K3 := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hK3
  set K2 := Om ((k : Ordinal.{0}) + 1 + 1) with hK2
  set Xh := S.psi (b + K2) (Om (1 + 1)) with hXhdef
  have hW3 : Le.leWe (K3 + 0) = K3 := by rw [add_zero]; exact Vn.vnWe_OmK k
  obtain ⟨-, -, -, hnorm, -⟩ := hB
  rw [hW3] at hnorm
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by have h := hnorm 0 zero_le; rwa [add_zero] at h
  have hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1))) := Xd.xdTr hl hX hβD hβD hβn
  have hbW : b < Om ω := (vbT_mem hl hX hβD).2
  have hAω : Om ω ≤ A := ConjT.OmW_le_A S _
  have hXSC : SC Xh := SC_psi hκ2 _
  have hXε : ω ^ Xh = Xh := gg_SC_eps hXSC
  have hX1 : Om 1 < Xh := (psiS_bounds (S := S) _ 1).1
  have hXω : ω ≤ Xh := (Lw.lw_omega_lt_SC hXSC).le
  -- the upper half
  have hD3 : VbD S l K3 := by
    have h := vbD_Om (S := S) (l := l) (k + 1 + 1); rwa [xiC2] at h
  have hβ3D : VbD S l (β + K3) :=
    ⟨CSet.add_mem hβD.1 hD3.1, CSet.add_mem hβD.2.1 hD3.2.1, vkOmW.1.isPrincipal hβD.2.2 hD3.2.2⟩
  have hT3K : vbT S l K3 = K2 := by
    have h := vbT_Om (S := S) hl hX (k := k + 1 + 1) (by omega); rwa [xiC2] at h
  have hT3 : vbT S l (β + K3) = b + K2 := by rw [Vh.vhT_add hl hX hβD hD3, hT3K]
  have hup := Xd.xdUp_at hl hX hA hρ (β + K3) hβ3D
  rw [hT3, add_assoc A 1, one_add_of_omega0_le hXω] at hup
  -- the own image of the base
  have hupβ := Xd.xdUp_at hl hX hA hρ β hβD
  set B := A + 1 + S.psi b (Om (1 + 1)) with hBdef
  have hAB : A ≤ B := le_self_add.trans le_self_add
  have hBown : B ∈ S.CSet B (S.psi B (Om 1)) :=
    CSet.add_mem (CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one hAB).2 hA) (CSet.one_mem _ _))
      (CSet.psi_mem (hbW.trans_le (hAω.trans hAB)) hκ2 (mxOm2_mem _ _)
        (Xd.xdT_leaf hl hX hβD hβn (hAω.trans hAB) hupβ))
  have hψb : 1 + S.psi b (Om (1 + 1)) < Xh := by
    rw [one_add_of_omega0_le (Lw.lw_omega_lt_SC (SC_psi hκ2 b)).le]
    exact psi_lt_psi_of_mem hκ2 (lt_add_of_pos_right b (Om_pos (add_pos_of_right zero_lt_one _).ne'))
      ((psi_mono (S := S) hκ2 le_self_add).2 hbn)
  have hρΘ : upsilon l ≤ gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) :=
    (gxTh_Om1 hZ hZ1 hAt).symm.le.trans (gxTh_mono (psiS_bounds (S := S) _ 1).1.le)
  intro Â hÂ hb
  have hX0 : Wv.wvX0 S l k β = Xh := rfl
  rw [hX0, gxTh_zero]
  simp only [add_zero]
  rw [Ua.uaOe_fix hXε hX1]
  unfold Le.leTe
  rw [Vn.vnWe_OmK k]
  have hAÂ : A ≤ Â := Sf.sfArg_le hA hÂ (by rw [hρ, ← hb]; exact hρΘ)
  have hÂB : Â ≤ B := Sf.sfArg_le hÂ hBown (by rw [← hb]; exact hupβ)
  have hδ : Â - A ≤ 1 + S.psi b (Om (1 + 1)) := by
    rw [Ordinal.sub_le, ← add_assoc]; exact hÂB
  have hab : (Â - A) + Xh = Xh :=
    Ordinal.add_absorp (a := Â - A) (b := Xh) (c := Xh) (by rw [hXε]; exact hδ.trans_lt hψb) (by rw [hXε])
  have hÂX : Â + Xh = A + Xh := by
    calc Â + Xh = A + (Â - A) + Xh := by rw [Ordinal.add_sub_cancel_of_le hAÂ]
      _ = A + Xh := by rw [add_assoc, hab]
  rw [hÂX]
  exact le_antisymm hup hlow

end Rst

/-- **THE IMAGE LAW AT EVERY LEVEL `k` FOR EVERY BASE `β ∈ D`** (the skeleton node `skX0LawDK`):
`Θ(ψ₂(β + Ω_{k+3})) = ψ₁(Â_β + Ω^{X̂⁰_k(β)})`, `X̂⁰_k(β) = ψ₂(T β + Ω_{k+2})`. -/
theorem xiLawDK (S : InaccSeq.{0}) :
    ∀ (k : ℕ) (l ηx A β : Ordinal.{0}), IsRestartIdx l → upsilon l < Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l → VbD S l β →
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 β →
      Wg.WgTopAt S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Wv.wvX0 S l k β) 0 β :=
  fun k _ _ _ _ hl hX hA hρ hβD hB => xiLaw_of_low hl hX hA hρ k hβD hB (xiLow hl hX hA hρ k _ hβD hB)

/-- `Ro.RoBaseE` at the base `Ω_{k+3}` (level `Ω_{k+3}`, exponent `0`) at every restart. -/
theorem xiBase_Om (k : ℕ) (l : Ordinal.{0}) :
    Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) := by
  have hW3 : Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + 0) = Om ((k : Ordinal.{0}) + 1 + 1 + 1) := by
    rw [add_zero, Vn.vnWe_OmK]
  have hK : Om ((k : Ordinal.{0}) + 1 + 1 + 1) < Om ω := Wv.wvOmK_lt_W k
  refine ⟨by rw [hW3], Vn.vnOmK3_mem k _ _, ?_, fun _ _ => Vn.vnOmK3_mem k _ _, ?_⟩
  · rw [hW3]
    exact (vkOmW.1.isPrincipal hK hK).trans_le (ConjT.OmW_le_A S _)
  · intro e' _ he'
    rw [nonpos_iff_eq_zero.1 he']
    exact (Om_pos one_ne_zero).trans (psiS_bounds (S := S) _ 1).1

/-- `Ro.RoBaseE` at the base `0` (level `Ω_{k+3}`, exponent `0`) at every restart. -/
theorem xiBase_zero (k : ℕ) (l : Ordinal.{0}) : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 0 := by
  have hW3 : Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + 0) = Om ((k : Ordinal.{0}) + 1 + 1 + 1) := by
    rw [add_zero, Vn.vnWe_OmK]
  refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun _ _ => CSet.zero_mem _ _, ?_⟩
  · rw [hW3, zero_add]
    exact (Wv.wvOmK_lt_W k).trans_le (ConjT.OmW_le_A S _)
  · intro e' _ he'
    rw [nonpos_iff_eq_zero.1 he']
    exact (Om_pos one_ne_zero).trans (psiS_bounds (S := S) _ 1).1

theorem xiD_zero (l : Ordinal.{0}) : VbD S l 0 :=
  ⟨CSet.zero_mem _ _, CSet.zero_mem _ _, Om_pos omega0_ne_zero⟩

theorem xiD_Om (k : ℕ) (l : Ordinal.{0}) : VbD S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) := by
  have h := vbD_Om (S := S) (l := l) (k + 1 + 1)
  rwa [xiC2] at h

/-- **The law at `k = 1`, `β = Ω₄`** (a REFUTE-FIRST test point): `Θ(ψ₂(Ω₄·2)) = ψ₁(Â + ψ₂(Ω₃·2))`. -/
theorem xiLaw_1_Om4 {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    Wg.WgTopAt S l (Om (((1 : ℕ) : Ordinal.{0}) + 1 + 1 + 1)) (Wv.wvX0 S l 1 (Om (((1 : ℕ) : Ordinal.{0}) + 1 + 1 + 1)))
      0 (Om (((1 : ℕ) : Ordinal.{0}) + 1 + 1 + 1)) :=
  xiLawDK S 1 l ηx A _ hl hX hA hρ (xiD_Om 1 l) (xiBase_Om 1 l)

/-- **The law at `k = 2`, `β = 0`** (a REFUTE-FIRST test point): `Θ(ψ₂(Ω₅)) = ψ₁(A + 1 + ψ₂(Ω₄))`. -/
theorem xiLaw_2_0 {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    Wg.WgTopAt S l (Om (((2 : ℕ) : Ordinal.{0}) + 1 + 1 + 1)) (Wv.wvX0 S l 2 0) 0 0 :=
  xiLawDK S 2 l ηx A 0 hl hX hA hρ (xiD_zero l) (xiBase_zero 2 l)

/-- **Non-vacuity of `xiLawDK`**: at the restart of `m* = L(0)` with its own `A`, every level `k` with the base
`Ω_{k+3}` (and the base `0`) satisfies every hypothesis. -/
theorem xiLawDK_wit (S : InaccSeq.{0}) :
    ∃ l ηx A : Ordinal.{0}, IsRestartIdx l ∧ upsilon l < Pv S ηx ∧ A ∈ S.CSet A (S.psi A (Om 1)) ∧
      S.psi A (Om 1) = upsilon l ∧ ∀ k : ℕ,
      (VbD S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) ∧
        Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) ∧
        Wg.WgTopAt S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1))
          (Wv.wvX0 S l k (Om ((k : Ordinal.{0}) + 1 + 1 + 1))) 0 (Om ((k : Ordinal.{0}) + 1 + 1 + 1))) ∧
      (VbD S l 0 ∧ Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 0 ∧
        Wg.WgTopAt S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Wv.wvX0 S l k 0) 0 0) := by
  obtain ⟨l, hl, -, hX, hA, hρ⟩ := Xd.xdWit S
  exact ⟨l, _, _, hl, hX, hA, hρ, fun k =>
    ⟨⟨xiD_Om k l, xiBase_Om k l, xiLawDK S k l _ _ _ hl hX hA hρ (xiD_Om k l) (xiBase_Om k l)⟩,
     ⟨xiD_zero l, xiBase_zero k l, xiLawDK S k l _ _ _ hl hX hA hρ (xiD_zero l) (xiBase_zero k l)⟩⟩⟩

end Googology.Trans.PoR.InaccPsi.R2.Xi

#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiT_mod
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiLowStep
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiLow
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiLaw_of_low
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiLawDK
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiBase_Om
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiBase_zero
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiLaw_1_Om4
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiLaw_2_0
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xi.xiLawDK_wit
