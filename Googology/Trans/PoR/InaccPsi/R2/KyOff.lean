import Googology.Trans.PoR.InaccPsi.R2.KxTop

/-!
# Ky: THE OFFSET LAW BELOW `Ω₃` ABOVE EVERY BASE WITH A LAW

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Vb.vbT S λ`, `D = Vb.VbD S λ`, `κ = Vb.vbK`.  Let `a ∈ D` be normal with
`Θ(ψ₂ a) = ψ₁(Â)`, `Â` own, `Ω_ω ≤ Â`.

* `kyLift` (**THE GENERIC LIFT WITHOUT `θ ∣ Â`**: `Xd.xdLift` with the difference `e − Â` read by `Kt.ktHCl_sub`);
* `kyLow` (**the lower half**: `ψ₁(Â + T δ) ≤ Θ(ψ₂(a + δ))` for `Ω₃ ∣ a`, `δ < Ω₃`, `a + δ` normal; the lift with the
  level bound `ζ ↦ T a + ζ`, since `T δ < ψ₂(T a + Ω₂) = T ψ₃(a + Ω₃)`);
* `kyUp` (**the upper half**: `Θ(ψ₂(a + δ)) ≤ ψ₁(Â + T δ)` for every `δ ∈ D`; one induction on `δ`, inside it one on the
  atoms below `ψ₂(a + δ)`, as `Xd.xdUp_at`);
* `kyOff` (**THE OFFSET LAW**: `Θ(ψ₂(a + δ)) = ψ₁(Â + T δ)` for `Ω₃ ∣ a`, `δ < Ω₃`, `a + δ` normal).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ky

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vk Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Kt
  Googology.Trans.PoR.InaccPsi.R2.Xd

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE GENERIC LIFT WITHOUT `θ ∣ Â`** (`Xd.xdLift` with the difference `e − Â` read by `Kt.ktHCl_sub`). -/
theorem kyLift {β Â Xb : Ordinal.{0}} (Lf : Ordinal.{0} → Ordinal.{0})
    (hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l)
    (hbase : S.psi Â (Om 1) ≤ gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))))
    (hXθ : Xb ≤ ConjT.th S) (hβH : β ∈ cdHull S l)
    (hβA : ∀ ζ, RxE S (rxW (upsilon l) (ldAtR S l)) ζ → ζ < Xb →
      β + rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) ζ < ConjT.Aη S (cdEta S l))
    (hβn : ∀ ζ, RxE S (rxW (upsilon l) (ldAtR S l)) ζ → ζ < Xb →
      β ∈ S.CSet (β + rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) ζ)
        (S.psi (β + rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) ζ) (Om (1 + 1))))
    (hL : ∀ ζ, RxE S (rxW (upsilon l) (ldAtR S l)) ζ → ζ < Xb →
      RxE S (rxW (upsilon l) (ldAtR S l)) (Lf ζ) ∧
      rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) (Lf ζ) ≤
        β + rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) ζ ∧
      ∀ x, x < ζ → x < S.psi (Lf ζ) (Om (1 + 1))) :
    ∀ ζ, RxE S (rxW (upsilon l) (ldAtR S l)) ζ → ζ < Xb →
      S.psi (Â + ζ) (Om 1) ≤
        gxTh (upsilon l) (ldAtR S l)
          (S.psi (β + rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) ζ) (Om (1 + 1))) := by
  obtain ⟨hZ, hZ1⟩ := Le.leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  set W := rxW (upsilon l) (ldAtR S l) with hWdef
  set κ := rxL S (upsilon l) (ldAtR S l) W with hκdef
  have hW : SC W := rxW_SC hZ hZ1 hAt
  have hθSC := ConjT.SC_th S
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt hκ2 _
  have hθW : ConjT.th S < Om ω := hθ2.trans vkOmW.2
  have hWA : Om ω ≤ ConjT.Aη S (cdEta S l) := ConjT.OmW_le_A S _
  have hEθ : ∀ {T ζ : Ordinal.{0}}, RxN S T ζ → ζ < ConjT.th S → RxE S T ζ :=
    fun hN hζ => ⟨hN, CSet.of_lt hζ, hζ.trans hθW⟩
  have hκH : ∀ ζ, RxE S W ζ → κ ζ ∈ S.CSet (ConjT.Aη S (cdEta S l)) (upsilon l) :=
    fun ζ hζ => rxL_memH hZ hZ1 hAt hW le_rfl hWA (fun g hg => by
      obtain ⟨hcode, hlt2, -⟩ := ruInv_spec (hg.trans_le (min_le_left _ _))
      exact (ldHull_iff hl hX hlt2).2 hcode) ζ hζ
  have hat : ∀ ζ, RxE S W ζ → ζ < Xb → S.psi (β + κ ζ) (Om (1 + 1)) ∈ ldAtR S l :=
    fun ζ hζ hζX => ⟨_, CSet.add_mem hβH (hκH ζ hζ), hβA ζ hζ hζX, rfl⟩
  have hpos : ∀ ζ, RxE S W ζ → ζ < Xb → ζ ≠ 0 →
      S.psi β (Om (1 + 1)) < S.psi (β + κ ζ) (Om (1 + 1)) := fun ζ hζ hζX h0 =>
    psi_lt_psi_of_mem hκ2 (lt_add_of_pos_right _ (rxL_pos hZ hZ1 hAt hζ h0)) (hβn ζ hζ hζX)
  set D : Set Ordinal.{0} := {ζ | RxE S W ζ ∧ ζ < Xb} with hDdef
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
    have hltX : e - Â < Xb := hlt.trans hζD.2
    have hltθ : e - Â < ConjT.th S := hltX.trans_le hXθ
    have hN : RxN S Tt (e - Â) := rxN_of_HCl hcnt.le (ktHCl_sub e he Â)
    have hET : RxE S Tt (e - Â) := hEθ hN hltθ
    refine ⟨⟨hET.mono hTW, hltX⟩, CSet.add_mem (hβn ζ hζD.1 hζD.2) ?_⟩
    obtain ⟨hLE, hKL, hxL⟩ := hL ζ hζD.1 hζD.2
    exact Wz.wzL_memL hZ hZ1 hAt htSC hTW hLE hKL (fun g hg' => CSet.of_lt (ruInv_spec hg').2.1) _ hET
      ⟨Lf ζ, le_rfl, CSet.of_lt (hxL _ hlt)⟩
  have hLift := rxLift hZ hZ1 hAt hβat hbase (D := D)
    (fun ζ hζ ζ' hζ' h => rxL_mono hZ hZ1 hAt hζ'.1 hζ.1 h)
    (fun ζ hζ => hat ζ hζ.1 hζ.2) (fun ζ hζ h0 => hpos ζ hζ.1 hζ.2 h0) hcl
  exact fun ζ hζ hζX => hLift ζ ⟨hζ, hζX⟩


/-- **The lower half of the offset law.** -/
theorem kyLow {a Â : Ordinal.{0}} (haD : VbD S l a) (h3 : Om (1 + 1 + 1) ∣ a)
    (han : a ∈ S.CSet a (S.psi a (Om (1 + 1))))
    (hbase : S.psi Â (Om 1) ≤ gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))))
    {δ : Ordinal.{0}} (hδD : VbD S l δ) (hδ3 : δ < Om (1 + 1 + 1))
    (hn : a + δ ∈ S.CSet (a + δ) (S.psi (a + δ) (Om (1 + 1)))) :
    S.psi (Â + vbT S l δ) (Om 1) ≤ gxTh (upsilon l) (ldAtR S l) (S.psi (a + δ) (Om (1 + 1))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hκ3 : S.InR (Om (1 + 1 + 1 : Ordinal.{0})) := InR_Om_succ (1 + 1)
  obtain ⟨hZ, hZ1⟩ := Le.leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hWA : Om ω ≤ ConjT.Aη S (cdEta S l) := ConjT.OmW_le_A S _
  have h3W : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 (by
    have := natCast_lt_omega0 3; push_cast at this; rwa [show (3 : Ordinal.{0}) = 1 + 1 + 1 by norm_num] at this)
  set b := vbT S l a with hbdef
  set Xb := S.psi (b + Om (1 + 1)) (Om (1 + 1)) with hXbdef
  obtain ⟨hbE, hbK⟩ := vbT_eq hl hX haD
  have hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1))) := xdTr hl hX haD haD han
  have hbm : b % Om (1 + 1) = 0 := xdT_mod hl hX a haD (Ordinal.mod_eq_zero_of_dvd h3)
  have hbW : b < Om ω := (vbT_mem hl hX haD).2
  have hXθ : Xb ≤ ConjT.th S := (psi_mono hκ2 (vkOmW.1.isPrincipal hbW ldOm2_lt_OmW).le).1
  set W := rxW (upsilon l) (ldAtR S l) with hWdef
  set κ := rxL S (upsilon l) (ldAtR S l) W with hκdef
  have hX2 : Xb < Om (1 + 1) := psi_lt hκ2 _
  have hκ3' : ∀ ζ, RxE S W ζ → ζ < Xb → κ ζ < Om (1 + 1 + 1) := fun ζ hζ hζX => by
    have h' := rxL_lt_lev hZ hZ1 hAt ζ hζ 1 (by rw [Nat.cast_one]; exact hζX.trans hX2)
    rwa [Nat.cast_one] at h'
  have hlift := kyLift hl hX (β := a) (Â := Â) (Xb := Xb) (fun ζ => b + ζ)
    ⟨a, haD.1, haD.2.2.trans_le hWA, rfl⟩ hbase hXθ haD.1
    (fun ζ hζ hζX => (vkOmW.1.isPrincipal haD.2.2 ((hκ3' ζ hζ hζX).trans h3W)).trans_le hWA)
    (fun ζ _ _ => CSet_mono le_self_add (psi_mono hκ2 le_self_add).1 han)
    (fun ζ hζ hζX => ⟨Vh.vhE_add hbE hζ, by
      show κ (b + ζ) ≤ a + κ ζ
      have hk : κ (b + ζ) = κ b + κ ζ := Vh.vhK_add hl hX b hbE ζ hζ
      rw [hk]
      have hb' : κ b = a := hbK
      rw [hb'],
      fun x hx => (xdLtPsi hbn hbm (hx.trans hζX)).trans_le (psi_mono hκ2 (add_le_add le_rfl hx.le)).1⟩)
  -- `T δ < ψ₂(T a + Ω₂)`
  obtain ⟨hδE, hδK⟩ := vbT_eq hl hX hδD
  have hda : a ≤ a + δ := le_self_add
  have hδm : δ ∈ S.CSet (a + δ) (S.psi (a + δ) (Om (1 + 1))) := by
    have h := (rxCDec (a + δ) hn).1 a (CSet_mono hda (psi_mono hκ2 hda).1 han) hda
    rwa [Ordinal.add_sub_cancel] at h
  have ha3 : a + δ ≤ a + Om (1 + 1 + 1) := add_le_add le_rfl hδ3.le
  have hψ23 : ∀ x y : Ordinal.{0}, S.psi x (Om (1 + 1)) ≤ S.psi y (Om (1 + 1 + 1)) := fun x y =>
    ((psi_lt hκ2 x).trans (psiS_bounds (S := S) y (1 + 1)).1).le
  have hδψ : δ < S.psi (a + Om (1 + 1 + 1)) (Om (1 + 1 + 1)) :=
    lt_psi_of_mem hκ3 (CSet_mono ha3 (hψ23 _ _) hδm) hδ3
  have h3D : VbD S l (Om (1 + 1 + 1)) := ⟨Kx.kxO3 _ _, Kx.kxO3 _ _, h3W⟩
  have ha3D : VbD S l (a + Om (1 + 1 + 1)) :=
    ⟨CSet.add_mem haD.1 h3D.1, CSet.add_mem haD.2.1 h3D.2.1, vkOmW.1.isPrincipal haD.2.2 h3W⟩
  have ha3n : a + Om (1 + 1 + 1) ∈ S.CSet (a + Om (1 + 1 + 1))
      (S.psi (a + Om (1 + 1 + 1)) (Om (1 + 1 + 1))) :=
    CSet.add_mem (CSet_mono le_self_add (hψ23 _ _) han) (Kx.kxO3 _ _)
  have hPD : VbD S l (S.psi (a + Om (1 + 1 + 1)) (Om (1 + 1 + 1))) :=
    ⟨CSet.psi_mem (ha3D.2.2.trans_le hWA) hκ3 (Kx.kxO3 _ _) ha3D.1,
      CSet.psi_mem ha3D.2.2 hκ3 (Kx.kxO3 _ _) ha3D.2.1, (psi_lt hκ3 _).trans h3W⟩
  have hT1 := vbT_mono hl hX hδD hPD hδψ
  have hTat := (vbT_atom hl hX (k := 1) le_rfl ha3D (by rw [Nat.cast_one]; exact ha3n)).1
  rw [Nat.cast_one] at hTat
  have hT3 : vbT S l (Om (1 + 1 + 1)) = Om (1 + 1) := by
    have h := vbT_Om hl hX (S := S) (l := l) (k := 2) (by norm_num)
    have e2 : ((2 : ℕ) : Ordinal.{0}) = 1 + 1 := by rw [Nat.cast_ofNat, one_add_one_eq_two]
    rwa [e2] at h
  rw [hTat, Vh.vhT_add hl hX haD h3D, hT3] at hT1
  have h := hlift (vbT S l δ) hδE hT1
  rwa [show rxL S (upsilon l) (ldAtR S l) (rxW (upsilon l) (ldAtR S l)) (vbT S l δ) = δ from hδK] at h

/-- **The upper half of the offset law**, every `δ ∈ D`. -/
theorem kyUp {a Â : Ordinal.{0}} (haD : VbD S l a) (han : a ∈ S.CSet a (S.psi a (Om (1 + 1))))
    (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1))) (hÂω : Om ω ≤ Â)
    (hlaw : gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) = S.psi Â (Om 1)) :
    ∀ δ, VbD S l δ →
      gxTh (upsilon l) (ldAtR S l) (S.psi (a + δ) (Om (1 + 1))) ≤ S.psi (Â + vbT S l δ) (Om 1) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, hρ1⟩ := vbZ hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hρa : upsilon l < gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) := by
    have h := gxTh_lt (Z := upsilon l) (At := ldAtR S l) GxCl.om (psiS_bounds (S := S) a 1).1
    rwa [gxTh_Om1 hρSC hρ1 hAt] at h
  intro δ
  induction δ using WellFoundedLT.induction with
  | ind δ IHo =>
  intro hδD
  set σ := S.psi (Â + vbT S l δ) (Om 1) with hσdef
  have hσSC : SC σ := SC_psi hκ1 _
  have hÂσ : S.psi Â (Om 1) ≤ σ := (psi_mono hκ1 le_self_add).1
  have hρσ : upsilon l < σ := (hρa.trans_eq hlaw).trans_le hÂσ
  have hadD : VbD S l (a + δ) :=
    ⟨CSet.add_mem haD.1 hδD.1, CSet.add_mem haD.2.1 hδD.2.1, vkOmW.1.isPrincipal haD.2.2 hδD.2.2⟩
  have hin : ∀ t, t ∈ ldAtR S l → t < S.psi (a + δ) (Om (1 + 1)) → gxTh (upsilon l) (ldAtR S l) t < σ := by
    intro t
    induction t using WellFoundedLT.induction with
    | ind t IHi =>
    intro ht hta
    have ht' := ht
    obtain ⟨a0, ha0C, ha0A, ht0⟩ := ht
    have hth : S.psi (a + δ) (Om (1 + 1)) < ConjT.th S :=
      psi_lt_psi_of_mem (InR_Om_succ 1) hadD.2.2 hadD.2.1
    have hb1 := psiS_bounds (S := S) a0 1
    rw [← ht0] at hb1
    have hVt : VbD S l t := by
      refine ⟨?_, CSet.of_lt (hta.trans hth), hb1.2.trans (Om_lt_Om.2 (by simpa using Vb.vbNat_lt_omega 0))⟩
      rw [ht0]; exact CSet.psi_mem ha0A (InR_Om_succ 1) (xdOm2_mem _ _) ha0C
    have hne : ¬ ∃ j : ℕ, t = Om (j : Ordinal.{0}) := fun ⟨j, hj⟩ => not_Om_of_between hb1.1 hb1.2 _ hj
    obtain ⟨k, hk, d, hdE, hdn, hxd, -⟩ :=
      rxE_atom hρ1.le (vbD_E hl hX hVt) (ht0 ▸ SC_psi (InR_Om_succ 1) a0) hb1.1 hne
    have hbk := psiS_bounds (S := S) d (k : Ordinal.{0})
    rw [← hxd] at hbk
    have hk1 : (k : Ordinal.{0}) = 1 := between_unique hbk.1 hbk.2 hb1.1 hb1.2
    have hdD : VbD S l d := vbD_atom hl hX (hxd ▸ hVt) hdE hdn hk
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
      have hδ₀D : VbD S l δ₀ := ⟨(rxCDec d hdD.1).1 a haD.1 had, (rxCDec d hdD.2.1).1 a haD.2.1 had,
        (Ordinal.sub_le_self d a).trans_lt hdD.2.2⟩
      have hO := IHo δ₀ hδ₀lt hδ₀D
      rw [← hd0] at hO
      have hatoms : ∀ s ∈ ldAtR S l, s < S.psi d (Om (1 + 1)) → gxTh (upsilon l) (ldAtR S l) s < σ :=
        fun s hs hsd => IHi s (hxd ▸ hsd) hs (hsd.trans hlt)
      have hδ₀C : δ₀ ∈ S.CSet d (S.psi d (Om (1 + 1))) :=
        (rxCDec d hdn).1 a (CSet_mono had (psi_mono hκ2 had).1 han) had
      have hTC : vbT S l δ₀ ∈ S.CSet (Â + vbT S l δ) σ := by
        refine xdT_cl hl hX (psi_lt (InR_Om_succ 1) d).le
          (fun e he _ => (vbT_mem hl hX he).2.trans_le (hÂω.trans le_self_add))
          (fun c hc hc2 hcC => ?_) δ₀ hδ₀D hδ₀C
        rw [vbT_code hl hX hc2 hc.1]
        exact CSet.of_lt (mxGx_bound hρSC hρ1 hAt hσSC hρσ hatoms c ((ldHull_iff hl hX hc2).1 hc.1)
          (lt_psi_of_mem (InR_Om_succ 1) hcC hc2))
      have hB : Â + vbT S l δ₀ < Â + vbT S l δ := (add_lt_add_iff_left _).2 (vbT_mono hl hX hδ₀D hδD hδ₀lt)
      have hBm : Â + vbT S l δ₀ ∈ S.CSet (Â + vbT S l δ) σ :=
        CSet.add_mem ((psi_mono hκ1 le_self_add).2 hÂ) hTC
      rw [hxd]
      exact hO.trans_lt (psi_lt_psi_of_mem hκ1 hB hBm)
  exact ldAtom_le hρSC hρ1 hAt hσSC hρσ hin

/-- **THE OFFSET LAW BELOW `Ω₃`.** -/
theorem kyOff {a Â : Ordinal.{0}} (haD : VbD S l a) (h3 : Om (1 + 1 + 1) ∣ a)
    (han : a ∈ S.CSet a (S.psi a (Om (1 + 1)))) (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1))) (hÂω : Om ω ≤ Â)
    (hlaw : gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) = S.psi Â (Om 1))
    {δ : Ordinal.{0}} (hδD : VbD S l δ) (hδ3 : δ < Om (1 + 1 + 1))
    (hn : a + δ ∈ S.CSet (a + δ) (S.psi (a + δ) (Om (1 + 1)))) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (a + δ) (Om (1 + 1))) = S.psi (Â + vbT S l δ) (Om 1) :=
  le_antisymm (kyUp hl hX haD han hÂ hÂω hlaw δ hδD) (kyLow hl hX haD h3 han hlaw.symm.le hδD hδ3 hn)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ky

#print axioms Googology.Trans.PoR.InaccPsi.R2.Ky.kyOff
