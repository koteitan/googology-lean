import Googology.Trans.PoR.InaccPsi.R2.UgOwn

/-!
# The first reading past the wall: `Θ_λ(ψ₂(β + ψ₃(0))) = ψ₁(Â + ψ₂(0))`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ₂(β + W^E)` (`Le.leTe`), `H_λ = cdHull S λ`,
`Γ₂ = Ua.uaGam = ψ₃(0)`, `ψ₁ = ψ_{Ω₁}`, `ψ₂ = ψ_{Ω₂}`, `f(a) = φ(a, 0)`, `X_k = Ud.udX k = f^{k+1}(Ω₂ + 1)`,
`T = Ua.uaTh S λ` (`= Ug.ugTh S λ` below `Γ₂`).

* `ugIt_mem`, `ugIt_cl` (the iterates `f^k(Ω₂ + 1)` are in every closure and are codes over every `Q > 1`),
  `ugIt_G`, `ugThIt` (**`T(f^{k+1}(Ω₂ + 1)) = f^{k+1}(Ω₁ + 1)`**), `ugThX_cof` (**the images `T X_k` are cofinal in
  `ψ₂(0)`**), `ugBase0` (`β = 0` is a base of every `W^{X_k}`);
* `ugTopX` (**the top law at `W^{X_k}`** from the level statement `Ud.udLevHi`: `Θ(ψ₂(β + W^{W^{X_k}})) =
  ψ₁(Â + Ω^{Ω^{T X_k}})` at every base `β` of `W^{X_k}` with `Θ(ψ₂(β)) = ψ₁(Â)`, `Â` own);
* `ugReadLim` (**THE READING AT A LIMIT EXPONENT**: from readings along a cofinal `ω`-sequence of exponents
  with cofinal images; no bound on the exponents);
* `ugRead` (**THE READING AT THE EXPONENT `ψ₃(0)`**: at a base `β` of every `W^{X_k}` with `Θ(ψ₂(β)) = ψ₁(Â)`,
  `Â` own, `Θ(ψ₂(β + Γ₂)) = ψ₁(Â + ψ₂(0))`, i.e. the top law `Θ(T_{Γ₂}(β)) = ψ₁(Â + Ω^{T Γ₂})` with
  `T Γ₂ = ψ₂(0)` (`Ug.ugGam`)), `ugRead0` (**`β = 0`: the reading of the first atom `ψ₂(ψ₃(0))` of
  `Ud.UdAtMove25`**), `ugReadT` (the same as the top law `Θ(T_{Γ₂}(β)) = ψ₁(Â + Ω^{T Γ₂})`), `ugReadA`
  (**`Θ(ψ₂(ψ₃(0))) = ψ₁(A + 1 + ψ₂(0))`** for every own `A` with `ψ₁(A) = ρ_λ`);
* `ugNoDown` (**the exponent `Ω₃` is not read as `Ω₂`**: `Θ_λ(ψ₂(Ω₃)) < ψ₁(A + 1 + Ω₂)`, so past `Y₃` the image
  cannot send `Ω₃ ↦ Ω₂`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ug

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Tg
  Googology.Trans.PoR.InaccPsi.R2.Tn Googology.Trans.PoR.InaccPsi.R2.Tx Googology.Trans.PoR.InaccPsi.R2.Ua
  Googology.Trans.PoR.InaccPsi.R2.Ud Googology.Trans.PoR.InaccPsi.R2.Rw

variable {S : InaccSeq.{0}}

theorem ugIt_mem (a b : Ordinal.{0}) :
    ∀ k : ℕ, (fun a : Ordinal.{0} => veblen a 0)^[k] (Om (1 + 1) + 1) ∈ S.CSet a b := by
  intro k
  induction k with
  | zero => exact CSet.succ_mem (mxOm2_mem a b)
  | succ k ih => rw [Function.iterate_succ_apply']; exact CSet.phi_mem ih (CSet.zero_mem _ _)

theorem ugIt_cl {Q : Ordinal.{0}} (hQ : SC Q) :
    ∀ k : ℕ, LeCl (Om (1 + 1)) Q ((fun a : Ordinal.{0} => veblen a 0)^[k] (Om (1 + 1) + 1)) := by
  intro k
  induction k with
  | zero => exact LeCl.add LeCl.om (LeCl.small (gg_one_lt_of_SC hQ))
  | succ k ih => rw [Function.iterate_succ_apply']; exact LeCl.phi ih (LeCl.zero hQ.1)

/-- `G = φ(Ω₂, 1) ≤ φ(a, 0)` for `a > Ω₂`. -/
theorem ugG_le_veb0 {a : Ordinal.{0}} (ha : Om (1 + 1) < a) : veblen (Om (1 + 1)) 1 ≤ veblen a 0 := by
  refine (veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨ha, ?_⟩))).le
  exact (gg_one_lt_of_SC ldOm2_SC).trans (ha.trans_le (left_le_veblen a 0))

theorem ugIt_G (k : ℕ) : veblen (Om (1 + 1)) 1 ≤ (fun a : Ordinal.{0} => veblen a 0)^[k + 1] (Om (1 + 1) + 1) := by
  rw [Function.iterate_succ_apply']; exact ugG_le_veb0 (udIt_lt k).2

/-- **The `X_k` are codes over every strongly critical `Q`.** -/
theorem ugX_cl {Q : Ordinal.{0}} (hQ : SC Q) (k : ℕ) : LeCl (Om (1 + 1)) Q (udX k) := ugIt_cl hQ (k + 1)

theorem ugX_mem (a b : Ordinal.{0}) (k : ℕ) : udX k ∈ S.CSet a b := ugIt_mem a b (k + 1)

/-- `β = 0` is a base of every `W^{X_k}`. -/
theorem ugBase0 (l : Ordinal.{0}) (k : ℕ) : RoBaseE S l (leWe (udX k)) 0 0 := by
  refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
  · rw [zero_add, add_zero]
    have hX3 : leWe (udX k) < uaGam := (leWe_lt_SC uaGam_spec.1 uaGam_spec.2 (udX_lt k)).1
    have hW3 : leWe (leWe (udX k)) < uaGam := (leWe_lt_SC uaGam_spec.1 uaGam_spec.2 hX3).1
    refine (hW3.trans_le (uaGam_le_G3 (S := S))).trans ((psi_lt (S := S) (InR_Om_succ (1 + 1)) _).trans ?_)
    exact Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _)
  · obtain rfl : e' = 0 := le_antisymm h' zero_le
    exact (SC_psi (InR_Om_succ 1) _).1

/-- **`ψ₂(0)` is below the least fixed point of `f` above `Ω₁`.** -/
theorem ugG1_le_nfp : S.psi 0 (Om (1 + 1)) ≤ nfp (fun a : Ordinal.{0} => veblen a 0) (Om 1 + 1) := by
  have hfp := nfp_fp isNormal_veblen_zero (Om (1 : Ordinal.{0}) + 1)
  have hgt : Om (1 : Ordinal.{0}) < nfp (fun a => veblen a 0) (Om 1 + 1) := (lt_add_one _).trans_le (le_nfp _ _)
  rw [lg_Gam_psi S]
  exact ggGam_le (Ru.ruSC_of_veblen ((Om_pos one_ne_zero).trans hgt) hfp) hgt

/-- **THE READING AT A LIMIT EXPONENT**: if `X` is a limit with exponents `E_k ≤ X` cofinal in it, the readings
`Θ(ψ₂(β + E_k)) = ψ₁(Â + y_k)` are known, and the `y_k ≤ Y` are cofinal in a limit `Y`, then
`Θ(ψ₂(β + X)) = ψ₁(Â + Y)`. -/
theorem ugReadLim {l β Â X Y : Ordinal.{0}} (E y : ℕ → Ordinal.{0}) (hXl : IsSuccLimit X) (hYl : IsSuccLimit Y)
    (hEX : ∀ k, E k ≤ X) (hEcof : ∀ e, e < X → ∃ k, e < E k) (hyY : ∀ k, y k ≤ Y)
    (hycof : ∀ z, z < Y → ∃ k, z ≤ y k)
    (hTop : ∀ k, gxTh (upsilon l) (ldAtR S l) (S.psi (β + E k) (Om (1 + 1))) = S.psi (Â + y k) (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + X) (Om (1 + 1))) = S.psi (Â + Y) (Om 1) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1)) := InR_Om_succ 1
  have hck : ∀ k, S.psi (β + E k) (Om (1 + 1)) ≤ S.psi (β + X) (Om (1 + 1)) := fun k =>
    (psi_mono hκ2 ((add_le_add_iff_left β).2 (hEX k))).1
  have hcofA : ∀ e, e < β + X → ∃ k, e < β + E k := by
    intro e he
    rcases lt_or_ge e β with heb | hbe
    · exact ⟨0, heb.trans_le le_self_add⟩
    · have e1 : e = β + (e - β) := (Ordinal.add_sub_cancel_of_le hbe).symm
      have h' : e - β < X := by
        have : β + (e - β) < β + X := by rw [← e1]; exact he
        exact (add_lt_add_iff_left _).1 this
      obtain ⟨k, hk⟩ := hEcof _ h'
      refine ⟨k, ?_⟩
      rw [e1]
      exact (add_lt_add_iff_left _).2 hk
  have hlimA : IsSuccLimit (β + X) := isSuccLimit_add β hXl
  apply le_antisymm
  · -- `≤`: every code below `ψ₂(β + X)` is below some `ψ₂(β + E_k)`
    haveI : Nonempty (Iio (S.psi (β + X) (Om (1 + 1)))) := ⟨⟨0, (SC_psi hκ2 _).1⟩⟩
    unfold gxTh
    rw [cdOtp_eq]
    refine ciSup_le fun ⟨xv, hxv⟩ => ?_
    dsimp only
    split_ifs with hx
    · have hxm : xv < S.psi (β + X) (Om (1 + 1)) := hxv
      rw [Lw.lw_psi_limit S hκ2 hlimA] at hxm
      have hbdd : BddAbove (range fun e : Iio (β + X) => S.psi e.1 (Om (1 + 1))) :=
        ⟨Om (1 + 1), by rintro _ ⟨e, rfl⟩; exact (psi_lt hκ2 _).le⟩
      haveI : Nonempty (Iio (β + X)) := ⟨⟨0, hlimA.bot_lt⟩⟩
      obtain ⟨⟨e, he⟩, hxe⟩ := (lt_ciSup_iff hbdd).1 hxm
      obtain ⟨k, hk⟩ := hcofA e he
      have hxc : xv < S.psi (β + E k) (Om (1 + 1)) := hxe.trans_le (psi_mono hκ2 hk.le).1
      have h1 := cdOtp_lt_of_mem hx hxc
      have h2 := hTop k
      unfold gxTh at h2
      rw [h2] at h1
      exact Order.add_one_le_of_lt (h1.trans_le (psi_mono hκ1 ((add_le_add_iff_left Â).2 (hyY k))).1)
    · exact zero_le
  · -- `≥`: `ψ₁` is continuous at the limit `Â + Y`
    have hlimB : IsSuccLimit (Â + Y) := isSuccLimit_add Â hYl
    rw [Lw.lw_psi_limit S hκ1 hlimB]
    haveI : Nonempty (Iio (Â + Y)) := ⟨⟨0, hlimB.bot_lt⟩⟩
    refine ciSup_le fun ⟨e, he⟩ => ?_
    have hk : ∃ k, e ≤ Â + y k := by
      rcases lt_or_ge e Â with heA | hAe
      · exact ⟨0, heA.le.trans le_self_add⟩
      · have e1 : e = Â + (e - Â) := (Ordinal.add_sub_cancel_of_le hAe).symm
        have h' : e - Â < Y := by
          have : Â + (e - Â) < Â + Y := by rw [← e1]; exact he
          exact (add_lt_add_iff_left _).1 this
        obtain ⟨k, hk⟩ := hycof _ h'
        refine ⟨k, ?_⟩
        rw [e1]
        exact (add_le_add_iff_left Â).2 hk
    obtain ⟨k, hk⟩ := hk
    calc S.psi e (Om 1) ≤ S.psi (Â + y k) (Om 1) := (psi_mono hκ1 hk).1
      _ = gxTh (upsilon l) (ldAtR S l) (S.psi (β + E k) (Om (1 + 1))) := (hTop k).symm
      _ ≤ gxTh (upsilon l) (ldAtR S l) (S.psi (β + X) (Om (1 + 1))) := gxTh_mono (hck k)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`T(f^{k+1}(Ω₂ + 1)) = f^{k+1}(Ω₁ + 1)`.** -/
theorem ugThIt : ∀ k : ℕ, uaTh S l ((fun a : Ordinal.{0} => veblen a 0)^[k + 1] (Om (1 + 1) + 1)) =
    (fun a : Ordinal.{0} => veblen a 0)^[k + 1] (Om 1 + 1) := by
  have h0H : (0 : Ordinal.{0}) ∈ cdHull S l := CSet.zero_mem _ _
  intro k
  induction k with
  | zero =>
    show uaTh S l (veblen (Om (1 + 1) + 1) 0) = veblen (Om 1 + 1) 0
    have hΩH : Om (1 + 1 : Ordinal.{0}) ∈ cdHull S l := mxOm2_mem _ _
    have h1 : Om (1 + 1 : Ordinal.{0}) + 1 < uaGam := uaGam_spec.1.isSuccLimit.add_one_lt uaGam_spec.2
    have hv := uaVeb hl hX (CSet.succ_mem hΩH) h0H (by simp) (ugG_le_veb0 (lt_add_one _))
      (uaGam_spec.1.2 _ h1 _ uaGam_spec.1.1)
    rw [hv, uaSucc hl hX hΩH h1, uaTh_lt tgOm_lt_G, txOm2 hl hX, uaTh_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply' _ (k + 1) (Om 1 + 1)]
    have hlt := udIt_lt (k + 1)
    have hv := uaVeb hl hX (ugIt_mem _ _ (k + 1)) h0H
      ((Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero)).trans hlt.2).ne'
      (ugG_le_veb0 hlt.2) (uaGam_spec.1.2 _ hlt.1 _ uaGam_spec.1.1)
    rw [hv, ih, uaTh_zero]

/-- **The images `T X_k` are cofinal in `ψ₂(0)`.** -/
theorem ugThX_cof {z : Ordinal.{0}} (hz : z < S.psi 0 (Om (1 + 1))) : ∃ k, z < uaTh S l (udX k) := by
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 (hz.trans_le ugG1_le_nfp)
  refine ⟨n, hn.trans_le ?_⟩
  unfold udX
  rw [ugThIt hl hX n, Function.iterate_succ_apply']
  exact left_le_veblen _ _

/-- **The top law at `W^{X_k}`.** -/
theorem ugTopX (k : ℕ) {β Â : Ordinal.{0}} (hb : RoBaseE S l (leWe (udX k)) 0 β)
    (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (leWe (udX k))) (Om (1 + 1))) =
      S.psi (Â + leOe (leOe (uaTh S l (udX k)))) (Om 1) := by
  have hXH : udX k ∈ cdHull S l := ugX_mem _ _ k
  have hGX : veblen (Om (1 + 1)) 1 ≤ udX k := ugIt_G k
  have hXG := udX_lt k
  have hlev := (udLevHi hl hX hXH hGX hXG).2
  have hG3 : 0 + leWe (udX k) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) := by
    rw [zero_add, ← udGam_eq]
    exact uaGam_spec.1.isPrincipal (leWe_lt_SC uaGam_spec.1 uaGam_spec.2 hXG).1 uaGam_spec.2
  have hG1 : 0 + leOe (uaTh S l (udX k)) + Om 1 < S.psi 0 (Om (1 + 1)) := by
    rw [zero_add]
    exact rwG_SC.isPrincipal (leOe_lt_SC rwG_SC rwO_lt_G (uaLtG1 hl hX _ hXH hXG)).1 rwO_lt_G
  have hcl : SnCL S (udX k) 0 0 := fun Q hQ _ => ugX_cl hQ k
  have htop := hlev 0 0 0 (Or.inl ⟨rfl, rfl⟩) (dvd_zero _) hG3 hG1 hcl
  rw [zero_add, zero_add] at htop
  have h := htop β Â hb zero_le hÂ hbase
  rw [gxTh_zero, add_zero] at h
  unfold leTe at h
  rw [add_zero] at h
  exact h

/-- **THE READING AT THE EXPONENT `ψ₃(0)`**: `Θ(ψ₂(β + Γ₂)) = ψ₁(Â + ψ₂(0))`. -/
theorem ugRead {β Â : Ordinal.{0}} (hb : ∀ k, RoBaseE S l (leWe (udX k)) 0 β)
    (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + uaGam) (Om (1 + 1))) = S.psi (Â + S.psi 0 (Om (1 + 1))) (Om 1) := by
  refine ugReadLim (l := l) (fun k => leWe (leWe (udX k))) (fun k => leOe (leOe (uaTh S l (udX k))))
    uaGam_spec.1.isSuccLimit rwG_SC.isSuccLimit (fun k => ?_) (fun e he => ?_) (fun k => ?_) (fun z hz => ?_)
    (fun k => ugTopX hl hX k (hb k) hÂ hbase)
  · exact (leWe_lt_SC uaGam_spec.1 uaGam_spec.2 (leWe_lt_SC uaGam_spec.1 uaGam_spec.2 (udX_lt k)).1).1.le
  · obtain ⟨k, hk⟩ := udX_cof he
    exact ⟨k, hk.trans_le ((tnLe_We _).trans (tnLe_We _))⟩
  · exact (leOe_lt_SC rwG_SC rwO_lt_G (leOe_lt_SC rwG_SC rwO_lt_G
      (uaLtG1 hl hX _ (ugX_mem _ _ k) (udX_lt k))).1).1.le
  · obtain ⟨k, hk⟩ := ugThX_cof hl hX hz
    exact ⟨k, hk.le.trans ((ugLeOe _).trans (ugLeOe _))⟩

/-- **The reading of the first atom `ψ₂(ψ₃(0))` of `Ud.UdAtMove25`**: `Θ(ψ₂(Γ₂)) = ψ₁(Â + ψ₂(0))` for `Â` own with
`Θ(ψ₂(0)) = ψ₁(Â)`. -/
theorem ugRead0 {Â : Ordinal.{0}} (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi 0 (Om (1 + 1))) = S.psi Â (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi uaGam (Om (1 + 1))) = S.psi (Â + S.psi 0 (Om (1 + 1))) (Om 1) := by
  have h := ugRead hl hX (β := 0) (fun k => ugBase0 l k) hÂ hbase
  rwa [zero_add] at h

/-- **The reading at `ψ₃(0)` as the top law of the image**: `Θ(ψ₂(β + W^{Γ₂})) = ψ₁(Â + Ω^{T Γ₂})`, `T = Ug.ugTh`. -/
theorem ugReadT {β Â : Ordinal.{0}} (hb : ∀ k, RoBaseE S l (leWe (udX k)) 0 β)
    (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (leTe S uaGam β) = S.psi (Â + leOe (ugTh S l uaGam)) (Om 1) := by
  have hW := (ugSC_W uaGam_spec.1 uaGam_spec.2).2
  have hε : ω ^ S.psi 0 (Om (1 + 1)) = S.psi 0 (Om (1 + 1)) := gg_SC_eps rwG_SC
  unfold leTe
  rw [hW, ugGam, uaOe_fix hε rwO_lt_G]
  exact ugRead hl hX hb hÂ hbase

/-- **The reading of the atom `ψ₂(ψ₃(0))` from the restart**: `Θ(ψ₂(Γ₂)) = ψ₁(A + 1 + ψ₂(0))` for every own `A`
with `ψ₁(A) = ρ_λ`. -/
theorem ugReadA {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi uaGam (Om (1 + 1))) = S.psi (A + 1 + S.psi 0 (Om (1 + 1))) (Om 1) := by
  have hÂ : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  exact ugRead0 hl hX hÂ (ldBlk_zero hA hρ)

/-- **THE IMAGE OF `Ω₃` IS NOT `Ω₂`**: `Θ_λ(ψ₂(Ω₃)) < ψ₁(A + 1 + Ω₂)` (`A = A_η` own), so the top law
`Θ(ψ₂(W^X)) = ψ₁(A + 1 + Ω^{T X})` with `T(Ω₃) = Ω₂` fails at `X = Ω₃ = W^{Ω₃}` (`Rn.rnTheta_at` bounds `Θ_λ(θ)`). -/
theorem ugNoDown (hown : ConjT.Aη S (cdEta S l) ∈
      S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1))) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1)) (Om (1 + 1))) <
      S.psi (ConjT.Aη S (cdEta S l) + 1 + Om (1 + 1)) (Om 1) := by
  set A := ConjT.Aη S (cdEta S l) with hA_def
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hρ0 : 0 < upsilon l := (leRho hl hX).1.1
  have hMW : 0 < Rn.rnMW S := (SC_psi (InR_Om_succ 1) _).1
  have h0 := Rn.rnTheta_at hl hX hown 0 (GxCl.zero hρ0) hMW
  rw [add_zero, gxTh_zero, add_zero] at h0
  have hθ : ConjT.th S = S.psi (Om ω) (Om (1 + 1)) := rfl
  rw [← hθ] at h0
  have hmono : gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1)) (Om (1 + 1))) ≤
      gxTh (upsilon l) (ldAtR S l) (ConjT.th S) :=
    gxTh_mono (psi_mono (InR_Om_succ 1) Ry.ryOm3_lt.le).1
  have hθW : ConjT.th S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
  have hlt : A + ConjT.th S + 1 < A + 1 + Om (1 + 1) := by
    have hω : (ω : Ordinal.{0}) ≤ Om (1 + 1) := (omega0_lt_Om (v := (1 + 1 : Ordinal.{0})) ugTwo_ne).le
    rw [add_assoc, add_assoc, Ordinal.one_add_of_omega0_le hω]
    exact (add_lt_add_iff_left A).2 (ldOm2_SC.isSuccLimit.add_one_lt hθW)
  have hWA : Om ω < A + ConjT.th S + 1 :=
    (ConjT.OmW_le_A S _).trans_lt (lt_of_lt_of_le (lt_add_of_pos_right A (Sf.sfTh_pos S)) le_self_add)
  have hAm := (psi_mono (S := S) hκ1 (le_self_add.trans le_self_add : A ≤ A + ConjT.th S + 1)).2 hown
  have hnf : A + ConjT.th S + 1 ∈ S.CSet (A + ConjT.th S + 1) (S.psi (A + ConjT.th S + 1) (Om 1)) :=
    CSet.add_mem (CSet.add_mem hAm (CSet.psi_mem hWA (InR_Om_succ 1) (mxOm2_mem _ _)
      (ConjT.OmW_mem S _ _))) (CSet.one_mem _ _)
  exact (hmono.trans h0).trans_lt (psi_lt_psi hκ1 hlt hnf)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ug
