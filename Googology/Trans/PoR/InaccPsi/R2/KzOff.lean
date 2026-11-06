import Googology.Trans.PoR.InaccPsi.R2.KzInv

/-!
# Kz: THE OFFSET LAW BELOW `Ω₃` ON `D_K` (`Ky.kyOff` below a bound `K`)

`Θ = gxTh ρ_λ (ldAtR λ)`, `T_K = vbTK S λ K`, `D_K = VbDK S λ K`, `κ = Vb.vbK`, `A = A_{η_λ}`.  Let `a ∈ D_K` be normal
with `Θ(ψ₂ a) = ψ₁(Â)`, `Â` own, `a ≤ Â`.

* `kzL_memL` (**the level shift with a level bound `L` on `RxEK`**: `Wz.wzL_memL` with the new case `κ Ω_ω = Ω_ω`);
* `vbTK_zero`, `kzT_mod` (`T_K 0 = 0`; `Ω₃ ∣ x ⇒ Ω₂ ∣ T_K x`, as `Xd.xdT_mod`);
* `kzLiftK` (**THE GENERIC LIFT BELOW `K`**: `Ky.kyLift` over `RxEK`; the domain of the lift also asks
  `β + κ ζ < A` and `κ ζ ∈ H_λ`, both closed downwards, so no bound `β + κ ζ < A` for all `ζ < X` is needed);
* `kzLowOff` (**the lower half**: `ψ₁(Â + T_K δ) ≤ Θ(ψ₂(a + δ))` for `Ω₃ ∣ a`, `δ < Ω₃`, `a + δ` normal, `a + δ < A`;
  `T_K δ < ψ₂(T_K a + Ω₂)` by `κ ψ₂(T_K a + Ω₂) = ψ₃(a + Ω₃)`);
* `kzUpOff` (**the upper half**: `Θ(ψ₂(a + δ)) ≤ ψ₁(Â + T_K δ)` for every `δ ∈ D_K`; the arguments `e < a + δ₀` are
  bounded through `T_K e < T_K a + T_K δ₀`, `T_K a ≤ a ≤ Â`);
* `kzOff` (**THE OFFSET LAW ON `D_K`**: `Θ(ψ₂(a + δ)) = ψ₁(Â + T_K δ)`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vk Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Kt
  Googology.Trans.PoR.InaccPsi.R2.Xd

variable {S : InaccSeq.{0}}

section K

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)
  {K : Ordinal.{0}} (hKB : KzB S K)
include hZ hZ1 hAt hKB

/-- **THE LEVEL SHIFT WITH A LEVEL BOUND `L` BELOW `K`.** -/
theorem kzL_memL {T a b L : Ordinal.{0}} (hT : SC T) (hTW : T ≤ rxW Z At)
    (hLE : RxEK S (rxW Z At) K L) (ha : rxL S Z At (rxW Z At) L ≤ a)
    (hinv : ∀ g, g < T → ruInv Z At g ∈ S.CSet a b) :
    ∀ x, RxEK S T K x → (∃ c, c ≤ L ∧ x ∈ S.CSet c (S.psi c (Om (1 + 1)))) →
      rxL S Z At (rxW Z At) x ∈ S.CSet a b := by
  have hW1 := rxW_le_Om1 (Z := Z) (At := At)
  have hT1 : T ≤ Om 1 := hTW.trans hW1
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  refine rxMs_ind (S := S) (T := rxW Z At) fun x IH hx hcx => ?_
  obtain ⟨c, hcn, hxc⟩ := hcx
  have hxW : RxEK S (rxW Z At) K x := ⟨hx.1.mono hTW, hx.2⟩
  rcases lt_or_ge x (Om 1) with h1 | h1
  · rw [(kzL_small hZ hZ1 hAt hxW h1).1]; exact hinv x (rxNs_lt_T hT (rxH_spec hx.1) h1)
  by_cases hΩ : ∃ j : ℕ, x = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    have hj : 1 ≤ j := by
      by_contra h0
      have : j = 0 := by omega
      subst this
      rw [Nat.cast_zero, Om_zero] at h1; exact absurd h1 (not_le.2 (Om_pos one_ne_zero))
    rw [rxL_Om hj]; exact rxC_Om_succ _ _ j
  by_cases hW : x = Om ω
  · rw [hW, kzL_OmW]; exact CSet.Om_mem (kzOmega_mem a b)
  have h1' : Om 1 < x := lt_of_le_of_ne h1 fun e => hΩ ⟨1, by rw [Nat.cast_one]; exact e.symm⟩
  by_cases hS : SC x
  · have hne : ∀ σ, x ≠ Om σ := fun σ e => by
      rcases kzCard hKB (e ▸ hx.2.2) with ⟨k, rfl⟩ | rfl
      · exact hΩ ⟨k, e⟩
      · exact hW e
    obtain ⟨j, hj, d, hdE, hdn, rfl, -⟩ := kzE_atom hKB hT1 hx hS h1' hne
    have hdEW : RxEK S (rxW Z At) K d := ⟨hdE.1.mono hTW, hdE.2⟩
    obtain ⟨hK, hdh⟩ := kzL_psiE hKB hj hdEW hdn
    have hdc : d < L ∧
        ∃ c', c' ≤ L ∧ d ∈ S.CSet c' (S.psi c' (Om (1 + 1))) := by
      rcases le_or_gt (S.psi c (Om (1 + 1))) (S.psi d (Om ((j : Ordinal.{0}) + 1))) with hle | hlt
      · have hL : S.psi c (Om (1 + 1)) ≤ S.Lam := (psi_lt hκ2 c).le.trans Wk.wkOm2_le_Lam
        obtain ⟨hdm, hdlt⟩ := arg_mem_of_psi_mem (InR_Om_succ _) hxc hle hL hdn
        exact ⟨hdlt.trans_le hcn, c, hcn, hdm⟩
      · have hj1 : j = 1 := by
          by_contra hne
          have hj2 : 2 ≤ j := by omega
          have h2 : Om (1 + 1 : Ordinal.{0}) ≤ Om (j : Ordinal.{0}) := by
            refine Om_le_Om.2 ?_
            rw [one_add_one_eq_two]; exact_mod_cast hj2
          have h3 := (psiS_bounds (S := S) d (j : Ordinal.{0})).1
          exact absurd ((h2.trans h3.le).trans_lt (hlt.trans (psi_lt hκ2 c))) (lt_irrefl _)
        subst hj1
        rw [Nat.cast_one] at hlt hdn
        have hdlt : d < c := by
          by_contra hcon
          exact absurd (psi_mono (S := S) hκ2 (not_lt.1 hcon)).1 (not_le.2 hlt)
        exact ⟨hdlt.trans_le hcn, d, (hdlt.trans_le hcn).le, hdn⟩
    obtain ⟨hdlt, hdI⟩ := hdc
    have hκd : rxL S Z At (rxW Z At) d < rxL S Z At (rxW Z At) L :=
      kzL_mono hZ hZ1 hAt hKB hdEW hLE hdlt
    rw [hK]
    exact CSet.psi_mem (hκd.trans_le ha) (InR_Om_succ _)
      (rxC_Om_succ2 _ _ j) (IH d (rxMs_lt_stage (kzE_lt_Lam hKB hdE) hdh) hdE hdI)
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, -, ha', hb⟩ := rxVeb h1' hε hS
    obtain ⟨haE, hbE, -, -⟩ := kzE_veb hx hv hb
    obtain ⟨-, -, hha, hhb⟩ := kzE_veb hxW hv hb
    obtain ⟨hac, hbc⟩ := rxCDecV hxc _ _ hv hb
    rw [kzL_veb hxW h1' hε hS]
    exact CSet.phi_mem (IH _ (rxMs_lt_val hha ha') haE ⟨c, hcn, hac⟩)
      (IH _ (rxMs_lt_val hhb hb) hbE ⟨c, hcn, hbc⟩)
  · have hlt := ruLog_lt h1' hε
    have hrlt : x % ω ^ log ω x < x := mod_opow_log_lt_self ω ((Om_pos one_ne_zero).trans h1').ne'
    obtain ⟨hlE, -⟩ := kzE_log hx
    obtain ⟨hrE, -⟩ := kzE_rem hx
    obtain ⟨-, hlh⟩ := kzE_log hxW
    obtain ⟨-, hrh⟩ := kzE_rem hxW
    have hlc : log ω x ∈ S.CSet c (S.psi c (Om (1 + 1))) := (rxCDec x hxc).2
    have hrc : x % ω ^ log ω x ∈ S.CSet c (S.psi c (Om (1 + 1))) := Wk.wkRem_mem hxc
    obtain ⟨m, hm⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
    rw [kzL_gt hxW h1' hlt, hm]
    have h1m := IH _ (rxMs_lt_val hlh hlt) hlE ⟨c, hcn, hlc⟩
    have h2m := IH _ (rxMs_lt_val hrh hrlt) hrE ⟨c, hcn, hrc⟩
    have hop : ω ^ rxL S Z At (rxW Z At) (log ω x) ∈ S.CSet a b := by
      have := CSet.phi_mem (S := S) (CSet.zero_mem a b) h1m; rwa [veblen_zero_apply] at this
    exact CSet.add_mem (ConjT.mul_nat_mem S hop m) h2m

end K

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)

include hl hX hKB

theorem vbTK_zero : vbTK S l K 0 = 0 := by
  have h := vbTK_K hl hX hKB (kzE_zero (T := vbW S l) hKB)
  rwa [kzK_zero hl hX hKB] at h

/-- **`Ω₃ ∣ x ⇒ Ω₂ ∣ T_K x`.** -/
theorem kzT_mod : ∀ x, VbDK S l K x → x % Om (1 + 1 + 1) = 0 → vbTK S l K x % Om (1 + 1) = 0 := by
  have h3 : (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  have h3ε : ω ^ Om (1 + 1 + 1) = (Om (1 + 1 + 1) : Ordinal.{0}) := gg_SC_eps (SC_Om h3)
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hm
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [vbTK_zero hl hX hKB, Ordinal.zero_mod]
  have hx3 : Om (1 + 1 + 1) ≤ x := by
    by_contra hc
    push Not at hc
    rw [Ordinal.mod_eq_of_lt hc] at hm
    exact hx0 hm
  have hx2 : Om (1 + 1) ≤ x := (Om_le_Om.2 le_self_add).trans hx3
  have hT2 : Om (1 + 1) ≤ vbTK S l K x := by
    have h := vbTK_ge_lev hl hX hKB hx 1 (by rw [Nat.cast_one]; exact hx3)
    rwa [Nat.cast_one] at h
  by_cases hε : ω ^ x = x
  · have he := vbTK_eps hl hX hKB hx hx2 hε
    rw [← he] at hT2 ⊢
    exact xdMod_opow hT2
  have hlog : log ω x < x := ruLog_lt ((Om_lt_Om.2 (lt_add_one 1)).trans_le hx2) hε
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hpos : (0 : Ordinal.{0}) < n := hn ▸ div_opow_log_pos ω hx0
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact lt_irrefl _ hpos)
  have hdm : x = ω ^ log ω x * n + x % ω ^ log ω x := by
    rw [← hn]; exact (Ordinal.div_add_mod x _).symm
  have hs : x % ω ^ log ω x < ω ^ log ω x := Ordinal.mod_lt x (opow_pos _ omega0_pos).ne'
  have hsx : x % ω ^ log ω x < x := hs.trans_le (opow_log_le_self ω hx0)
  have hxE := vbDK_E hl hX hx
  obtain ⟨heD, -, -⟩ := vbDK_log hx hxE
  obtain ⟨hsD, -, -⟩ := vbDK_rem hx hxE
  have he3 : Om (1 + 1 + 1) ≤ log ω x := le_log_of_opow_le one_lt_omega0 (by rw [h3ε]; exact hx3)
  have e1 : (ω ^ log ω x * n + x % ω ^ log ω x) % Om (1 + 1 + 1) =
      (x % ω ^ log ω x) % Om (1 + 1 + 1) := xdModHead h3ε he3 n
  rw [← hdm, hm] at e1
  have hTs := IH _ hsx hsD e1.symm
  have hTe : Om (1 + 1) ≤ vbTK S l K (log ω x) := by
    have h := vbTK_ge_lev hl hX hKB heD 1 (by rw [Nat.cast_one]; exact he3)
    rwa [Nat.cast_one] at h
  rw [(congrArg (vbTK S l K) hdm).trans (kzT_cnf hl hX hKB n hn1 heD hsD hs), xdModHead Ru.ruOm2_eps hTe n]
  exact hTs

/-- **THE GENERIC LIFT BELOW `K`.** -/
theorem kzLiftK {β Â Xb : Ordinal.{0}} (Lf : Ordinal.{0} → Ordinal.{0})
    (hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l)
    (hbase : S.psi Â (Om 1) ≤ gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))))
    (hXθ : Xb ≤ S.psi K (Om (1 + 1))) (hβH : β ∈ cdHull S l)
    (hβn : ∀ ζ, RxEK S (rxW (upsilon l) (ldAtR S l)) K ζ → ζ < Xb →
      β ∈ S.CSet (β + rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) ζ)
        (S.psi (β + rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) ζ) (Om (1 + 1))))
    (hL : ∀ ζ, RxEK S (rxW (upsilon l) (ldAtR S l)) K ζ → ζ < Xb →
      RxEK S (rxW (upsilon l) (ldAtR S l)) K (Lf ζ) ∧
      rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) (Lf ζ) ≤
        β + rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) ζ ∧
      ∀ x, x < ζ → x < S.psi (Lf ζ) (Om (1 + 1))) :
    ∀ ζ, RxEK S (rxW (upsilon l) (ldAtR S l)) K ζ → ζ < Xb →
      β + rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) ζ < ConjT.Aη S (cdEta S l) →
      rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) ζ ∈ cdHull S l →
      S.psi (Â + ζ) (Om 1) ≤
        gxTh (upsilon l) (ldAtR S l)
          (S.psi (β + rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) ζ) (Om (1 + 1))) := by
  obtain ⟨hZ, hZ1⟩ := Le.leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  set W := rxW (upsilon l) (ldAtR S l) with hWdef
  set κ := rxL S (upsilon l) (ldAtR S l) W with hκdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hψK : S.psi K (Om (1 + 1)) < K :=
    ((psi_lt hκ2 K).trans (Om_lt_Om.2 (by simpa using Vb.vbNat_lt_omega 0))).trans_le hKB.ge
  have hEθ : ∀ {T ζ : Ordinal.{0}}, RxN S T ζ → ζ < S.psi K (Om (1 + 1)) → RxEK S T K ζ :=
    fun hN hζ => ⟨hN, CSet.of_lt hζ, hζ.trans hψK⟩
  have hinvH : ∀ g, g < W → ruInv (upsilon l) (ldAtR S l) g ∈ cdHull S l := fun g hg => by
    obtain ⟨hcode, hlt2, -⟩ := ruInv_spec (hg.trans_le (min_le_left _ _))
    exact (ldHull_iff hl hX hlt2).2 hcode
  set D : Set Ordinal.{0} :=
    {ζ | RxEK S W K ζ ∧ ζ < Xb ∧ β + κ ζ < ConjT.Aη S (cdEta S l) ∧ κ ζ ∈ cdHull S l} with hDdef
  have hat : ∀ ζ ∈ D, S.psi (β + κ ζ) (Om (1 + 1)) ∈ ldAtR S l :=
    fun ζ hζ => ⟨_, CSet.add_mem hβH hζ.2.2.2, hζ.2.2.1, rfl⟩
  have hpos : ∀ ζ ∈ D, ζ ≠ 0 → S.psi β (Om (1 + 1)) < S.psi (β + κ ζ) (Om (1 + 1)) := fun ζ hζ h0 =>
    psi_lt_psi_of_mem hκ2 (lt_add_of_pos_right _ (kzL_pos hZ hZ1 hAt hKB hζ.1 h0)) (hβn ζ hζ.1 hζ.2.1)
  have hcl : ∀ ζ ∈ D, gxTh (upsilon l) (ldAtR S l) (S.psi (β + κ ζ) (Om (1 + 1))) < Om 1 →
      ∀ e, HCl S (Â + ζ) (gxTh (upsilon l) (ldAtR S l) (S.psi (β + κ ζ) (Om (1 + 1)))) e →
      Â ≤ e → e < Â + ζ → e - Â ∈ D ∧
        β + κ (e - Â) ∈ S.CSet (β + κ ζ) (S.psi (β + κ ζ) (Om (1 + 1))) := by
    intro ζ hζD hcnt e he h1 h2
    set t := S.psi (β + κ ζ) (Om (1 + 1)) with htdef
    set Tt := gxTh (upsilon l) (ldAtR S l) t with hTtdef
    have htSC : SC Tt :=
      gxTh_SC hZ hAt (SC_psi hκ2 _) (hZ1.trans (psiS_bounds (S := S) _ 1).1)
    have hTZ : Tt ≤ gxTh (upsilon l) (ldAtR S l) (Om (1 + 1)) := gxTh_mono (psi_lt hκ2 _).le
    have hTW : Tt ≤ W := le_min hTZ hcnt.le
    have hlt : e - Â < ζ := Ry.rySub_lt h1 h2
    have hltX : e - Â < Xb := hlt.trans hζD.2.1
    have hN : RxN S Tt (e - Â) := rxN_of_HCl hcnt.le (ktHCl_sub e he Â)
    have hET : RxEK S Tt K (e - Â) := hEθ hN (hltX.trans_le hXθ)
    have hETW : RxEK S W K (e - Â) := ⟨hET.1.mono hTW, hET.2⟩
    have hmono : κ (e - Â) < κ ζ := kzL_mono hZ hZ1 hAt hKB hETW hζD.1 hlt
    obtain ⟨hLE, hKL, hxL⟩ := hL ζ hζD.1 hζD.2.1
    have hcx : ∃ c, c ≤ Lf ζ ∧ e - Â ∈ S.CSet c (S.psi c (Om (1 + 1))) :=
      ⟨Lf ζ, le_rfl, CSet.of_lt (hxL _ hlt)⟩
    have hmemL := kzL_memL hZ hZ1 hAt hKB htSC hTW hLE hKL
      (fun g hg' => CSet.of_lt (ruInv_spec hg').2.1) _ hET hcx
    have hHull : κ (e - Â) ∈ cdHull S l :=
      kzL_memL hZ hZ1 hAt hKB htSC hTW hLE (hKL.trans hζD.2.2.1.le)
        (fun g hg' => hinvH g (hg'.trans_le hTW)) _ hET hcx
    exact ⟨⟨hETW, hltX, ((add_lt_add_iff_left β).2 hmono).trans hζD.2.2.1, hHull⟩,
      CSet.add_mem (hβn ζ hζD.1 hζD.2.1) hmemL⟩
  have hLift := rxLift hZ hZ1 hAt hβat hbase (D := D)
    (fun ζ hζ ζ' hζ' h => kzL_mono hZ hZ1 hAt hKB hζ'.1 hζ.1 h) hat hpos hcl
  exact fun ζ hζ hζX hA hH => hLift ζ ⟨hζ, hζX, hA, hH⟩

/-- **The lower half of the offset law on `D_K`.** -/
theorem kzLowOff {a Â : Ordinal.{0}} (haD : VbDK S l K a) (h3 : Om (1 + 1 + 1) ∣ a)
    (han : a ∈ S.CSet a (S.psi a (Om (1 + 1))))
    (hbase : S.psi Â (Om 1) ≤ gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))))
    {δ : Ordinal.{0}} (hδD : VbDK S l K δ) (hδ3 : δ < Om (1 + 1 + 1))
    (hn : a + δ ∈ S.CSet (a + δ) (S.psi (a + δ) (Om (1 + 1))))
    (hδA : a + δ < ConjT.Aη S (cdEta S l)) :
    S.psi (Â + vbTK S l K δ) (Om 1) ≤ gxTh (upsilon l) (ldAtR S l) (S.psi (a + δ) (Om (1 + 1))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hκ3 : S.InR (Om (1 + 1 + 1 : Ordinal.{0})) := InR_Om_succ (1 + 1)
  obtain ⟨hZ, hZ1⟩ := Le.leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have e2 : ((2 : ℕ) : Ordinal.{0}) = 1 + 1 := by rw [Nat.cast_ofNat, one_add_one_eq_two]
  have h2K : Om (1 + 1 : Ordinal.{0}) < K :=
    (Om_lt_Om.2 (by simpa using Vb.vbNat_lt_omega 0)).trans_le hKB.ge
  set b := vbTK S l K a with hbdef
  set Xb := S.psi (b + Om (1 + 1)) (Om (1 + 1)) with hXbdef
  obtain ⟨hbE, hbK⟩ := vbTK_eq hl hX hKB haD
  have hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1))) := kzTr hl hX hKB haD haD han
  have hbm : b % Om (1 + 1) = 0 := kzT_mod hl hX hKB a haD (Ordinal.mod_eq_zero_of_dvd h3)
  have hXθ : Xb ≤ S.psi K (Om (1 + 1)) := (psi_mono hκ2 (hKB.sc.isPrincipal hbE.2.2 h2K).le).1
  set W := rxW (upsilon l) (ldAtR S l) with hWdef
  set κ := rxL S (upsilon l) (ldAtR S l) W with hκdef
  have hlift := kzLiftK hl hX hKB (β := a) (Â := Â) (Xb := Xb) (fun ζ => b + ζ)
    ⟨a, haD.1, le_self_add.trans_lt hδA, rfl⟩ hbase hXθ haD.1
    (fun ζ _ _ => CSet_mono le_self_add (psi_mono hκ2 le_self_add).1 han)
    (fun ζ hζ hζX => ⟨kzE_add hKB hbE hζ, by
      show κ (b + ζ) ≤ a + κ ζ
      have hk : κ (b + ζ) = κ b + κ ζ := kzK_add hl hX hKB b hbE ζ hζ
      rw [hk]
      have hb' : κ b = a := hbK
      rw [hb'],
      fun x hx => (xdLtPsi hbn hbm (hx.trans hζX)).trans_le (psi_mono hκ2 (add_le_add le_rfl hx.le)).1⟩)
  -- `T δ < ψ₂(T a + Ω₂)`, through `κ ψ₂(T a + Ω₂) = ψ₃(a + Ω₃)`
  obtain ⟨hδE, hδK⟩ := vbTK_eq hl hX hKB hδD
  have hda : a ≤ a + δ := le_self_add
  have hδm : δ ∈ S.CSet (a + δ) (S.psi (a + δ) (Om (1 + 1))) := by
    have h := (rxCDec (a + δ) hn).1 a (CSet_mono hda (psi_mono hκ2 hda).1 han) hda
    rwa [Ordinal.add_sub_cancel] at h
  have ha3 : a + δ ≤ a + Om (1 + 1 + 1) := add_le_add le_rfl hδ3.le
  have hψ23 : ∀ x y : Ordinal.{0}, S.psi x (Om (1 + 1)) ≤ S.psi y (Om (1 + 1 + 1)) := fun x y =>
    ((psi_lt hκ2 x).trans (psiS_bounds (S := S) y (1 + 1)).1).le
  have hδψ : δ < S.psi (a + Om (1 + 1 + 1)) (Om (1 + 1 + 1)) :=
    lt_psi_of_mem hκ3 (CSet_mono ha3 (hψ23 _ _) hδm) hδ3
  have h2E : RxEK S W K (Om (1 + 1)) := by
    have h : RxEK S W K (Om ((2 : ℕ) : Ordinal.{0})) :=
      ⟨RxN.om (rxN_nat 2), rxC_Om_nat _ _ 2, (Om_lt_Om.2 (natCast_lt_omega0 2)).trans_le hKB.ge⟩
    rwa [e2] at h
  have hbΩE : RxEK S W K (b + Om (1 + 1)) := kzE_add hKB hbE h2E
  have hbΩn : b + Om (1 + 1) ∈ S.CSet (b + Om (1 + 1)) (S.psi (b + Om (1 + 1)) (Om ((1 : ℕ) + 1))) := by
    rw [Nat.cast_one]
    exact CSet.add_mem (CSet_mono le_self_add (psi_mono hκ2 le_self_add).1 hbn) (xdOm2_mem _ _)
  have hyE : RxEK S W K Xb := by
    have h := kzE_psi hKB (k := 1) le_rfl hbΩE hbΩn
    rwa [Nat.cast_one] at h
  have hK2 : κ (Om (1 + 1)) = Om (1 + 1 + 1) := by
    have h : κ (Om ((2 : ℕ) : Ordinal.{0})) = Om (((2 : ℕ) : Ordinal.{0}) + 1) := rxL_Om (by norm_num)
    rwa [e2] at h
  have hyK : κ Xb = S.psi (a + Om (1 + 1 + 1)) (Om (1 + 1 + 1)) := by
    have h := (kzL_psiE (Z := upsilon l) (At := ldAtR S l) hKB (k := 1) le_rfl hbΩE hbΩn).1
    rw [Nat.cast_one] at h
    have hadd : rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) (b + Om (1 + 1)) =
        a + Om (1 + 1 + 1) := by
      have h1 : κ (b + Om (1 + 1)) = κ b + κ (Om (1 + 1)) := kzK_add hl hX hKB b hbE _ h2E
      have hb' : κ b = a := hbK
      rw [hb', hK2] at h1; exact h1
    rw [hadd] at h; exact h
  have hδK' : κ (vbTK S l K δ) = δ := hδK
  have hT1 : vbTK S l K δ < Xb := (vbKK_lt_iff hl hX hKB hδE hyE).2 (by
    show κ (vbTK S l K δ) < κ Xb
    rw [hδK', hyK]; exact hδψ)
  have hδK'' : rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) (vbTK S l K δ) = δ := hδK
  have h := hlift (vbTK S l K δ) hδE hT1 (by rw [hδK'']; exact hδA) (by rw [hδK'']; exact hδD.1)
  rwa [hδK''] at h

/-- **The upper half of the offset law on `D_K`**, every `δ ∈ D_K`. -/
theorem kzUpOff {a Â : Ordinal.{0}} (haD : VbDK S l K a) (han : a ∈ S.CSet a (S.psi a (Om (1 + 1))))
    (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1))) (hÂa : a ≤ Â)
    (hlaw : gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) = S.psi Â (Om 1)) :
    ∀ δ, VbDK S l K δ →
      gxTh (upsilon l) (ldAtR S l) (S.psi (a + δ) (Om (1 + 1))) ≤ S.psi (Â + vbTK S l K δ) (Om 1) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, hρ1⟩ := vbZ hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hρa : upsilon l < gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) := by
    have h := gxTh_lt (Z := upsilon l) (At := ldAtR S l) GxCl.om (psiS_bounds (S := S) a 1).1
    rwa [gxTh_Om1 hρSC hρ1 hAt] at h
  have hTaÂ : vbTK S l K a ≤ Â := (vbTK_le_self hl hX hKB haD).trans hÂa
  intro δ
  induction δ using WellFoundedLT.induction with
  | ind δ IHo =>
  intro hδD
  set σ := S.psi (Â + vbTK S l K δ) (Om 1) with hσdef
  have hσSC : SC σ := SC_psi hκ1 _
  have hÂσ : S.psi Â (Om 1) ≤ σ := (psi_mono hκ1 le_self_add).1
  have hρσ : upsilon l < σ := (hρa.trans_eq hlaw).trans_le hÂσ
  have hadD : VbDK S l K (a + δ) :=
    ⟨CSet.add_mem haD.1 hδD.1, CSet.add_mem haD.2.1 hδD.2.1, hKB.sc.isPrincipal haD.2.2 hδD.2.2⟩
  have hin : ∀ t, t ∈ ldAtR S l → t < S.psi (a + δ) (Om (1 + 1)) → gxTh (upsilon l) (ldAtR S l) t < σ := by
    intro t
    induction t using WellFoundedLT.induction with
    | ind t IHi =>
    intro ht hta
    have ht' := ht
    obtain ⟨a0, ha0C, ha0A, ht0⟩ := ht
    have hth : S.psi (a + δ) (Om (1 + 1)) < S.psi K (Om (1 + 1)) :=
      psi_lt_psi_of_mem (InR_Om_succ 1) hadD.2.2 hadD.2.1
    have hb1 := psiS_bounds (S := S) a0 1
    rw [← ht0] at hb1
    have hVt : VbDK S l K t := by
      refine ⟨?_, CSet.of_lt (hta.trans hth),
        (hb1.2.trans (Om_lt_Om.2 (by simpa using Vb.vbNat_lt_omega 0))).trans_le hKB.ge⟩
      rw [ht0]; exact CSet.psi_mem ha0A (InR_Om_succ 1) (xdOm2_mem _ _) ha0C
    have hne : ¬ ∃ j : ℕ, t = Om (j : Ordinal.{0}) := fun ⟨j, hj⟩ => not_Om_of_between hb1.1 hb1.2 _ hj
    have htW : t ≠ Om ω := fun e => by
      rw [e] at hb1
      exact absurd (hb1.2.trans (Om_lt_Om.2 (by simpa using Vb.vbNat_lt_omega 0))) (lt_irrefl _)
    obtain ⟨k, hk, d, hdE, hdn, hxd, -⟩ :=
      kzE_atom hKB hρ1.le (vbDK_E hl hX hVt) (ht0 ▸ SC_psi (InR_Om_succ 1) a0) hb1.1
        (kzNe hKB (vbDK_E hl hX hVt) hne htW)
    have hbk := psiS_bounds (S := S) d (k : Ordinal.{0})
    rw [← hxd] at hbk
    have hk1 : (k : Ordinal.{0}) = 1 := between_unique hbk.1 hbk.2 hb1.1 hb1.2
    have hdD : VbDK S l K d := vbDK_atom hl hX (hxd ▸ hVt) hdE hdn hk
    rw [hk1] at hxd hdn
    have hlt : S.psi d (Om (1 + 1)) < S.psi (a + δ) (Om (1 + 1)) := hxd ▸ hta
    have hdaδ : d < a + δ := by
      by_contra hc
      exact absurd hlt (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) (not_lt.1 hc)).1)
    rcases lt_or_ge d a with hda | had
    · have htA : t < S.psi a (Om (1 + 1)) := by
        rw [hxd]; exact psi_lt_psi_of_mem hκ2 hda (CSet_mono hda.le (psi_mono hκ2 hda.le).1 hdn)
      exact (gxTh_lt (GxCl.atom ht') htA).trans_le (hlaw ▸ hÂσ)
    · set δ₀ := d - a with hδ₀def
      have hd0 : d = a + δ₀ := (Ordinal.add_sub_cancel_of_le had).symm
      have hδ₀lt : δ₀ < δ := by
        have h := hdaδ; rw [hd0] at h; exact (add_lt_add_iff_left a).1 h
      have hδ₀D : VbDK S l K δ₀ := ⟨(rxCDec d hdD.1).1 a haD.1 had, (rxCDec d hdD.2.1).1 a haD.2.1 had,
        (Ordinal.sub_le_self d a).trans_lt hdD.2.2⟩
      have hO := IHo δ₀ hδ₀lt hδ₀D
      rw [← hd0] at hO
      have hatoms : ∀ s ∈ ldAtR S l, s < S.psi d (Om (1 + 1)) → gxTh (upsilon l) (ldAtR S l) s < σ :=
        fun s hs hsd => IHi s (hxd ▸ hsd) hs (hsd.trans hlt)
      have hδ₀C : δ₀ ∈ S.CSet d (S.psi d (Om (1 + 1))) :=
        (rxCDec d hdn).1 a (CSet_mono had (psi_mono hκ2 had).1 han) had
      -- `T e < T d = T a + T δ₀ < T a + T δ ≤ Â + T δ` for the arguments `e < d`
      have hTd : vbTK S l K d < Â + vbTK S l K δ := by
        rw [hd0, kzT_add hl hX hKB haD hδ₀D]
        exact ((add_lt_add_iff_left _).2 (vbTK_mono hl hX hKB hδ₀D hδD hδ₀lt)).trans_le
          (add_le_add_left hTaÂ _)
      have hTC : vbTK S l K δ₀ ∈ S.CSet (Â + vbTK S l K δ) σ := by
        refine kzT_cl hl hX hKB (psi_lt (InR_Om_succ 1) d).le
          (fun e he hed => (vbTK_mono hl hX hKB he hdD hed).trans hTd)
          (fun c hc hc2 hcC => ?_) δ₀ hδ₀D hδ₀C
        rw [vbTK_code hl hX hKB hc2 hc.1]
        exact CSet.of_lt (mxGx_bound hρSC hρ1 hAt hσSC hρσ hatoms c ((ldHull_iff hl hX hc2).1 hc.1)
          (lt_psi_of_mem (InR_Om_succ 1) hcC hc2))
      have hB : Â + vbTK S l K δ₀ < Â + vbTK S l K δ :=
        (add_lt_add_iff_left _).2 (vbTK_mono hl hX hKB hδ₀D hδD hδ₀lt)
      have hBm : Â + vbTK S l K δ₀ ∈ S.CSet (Â + vbTK S l K δ) σ :=
        CSet.add_mem ((psi_mono hκ1 le_self_add).2 hÂ) hTC
      rw [hxd]
      exact hO.trans_lt (psi_lt_psi_of_mem hκ1 hB hBm)
  exact ldAtom_le hρSC hρ1 hAt hσSC hρσ hin

/-- **THE OFFSET LAW ON `D_K`.** -/
theorem kzOff {a Â : Ordinal.{0}} (haD : VbDK S l K a) (h3 : Om (1 + 1 + 1) ∣ a)
    (han : a ∈ S.CSet a (S.psi a (Om (1 + 1)))) (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1))) (hÂa : a ≤ Â)
    (hlaw : gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) = S.psi Â (Om 1))
    {δ : Ordinal.{0}} (hδD : VbDK S l K δ) (hδ3 : δ < Om (1 + 1 + 1))
    (hn : a + δ ∈ S.CSet (a + δ) (S.psi (a + δ) (Om (1 + 1))))
    (hδA : a + δ < ConjT.Aη S (cdEta S l)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (a + δ) (Om (1 + 1))) = S.psi (Â + vbTK S l K δ) (Om 1) :=
  le_antisymm (kzUpOff hl hX hKB haD han hÂ hÂa hlaw δ hδD)
    (kzLowOff hl hX hKB haD h3 han hlaw.symm.le hδD hδ3 hn hδA)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Kz

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kz.kzOff
