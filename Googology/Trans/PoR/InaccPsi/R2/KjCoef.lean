import Googology.Trans.PoR.InaccPsi.R2.KiPoly

/-!
# Kj: THE TOP LAW AT EVERY NORMAL `b = β + W^E·γ`, `E = Ω_{k+3} + W-polynomial + e`, every code `γ ≥ 1`

`Θ`, `T`, `A`, `W^x = leWe x`, `Ω^x = leOe x`, `Zd.ZdLaw`, `Ki.kiX`, `Ki.KiValid` as before.  `Ki.kiTop` is `γ = 1`.

* `kjE_mem` (`E` is a member once its components are), `kjComp` (**the components of `E` lie below `ψ₂(β + W^E)`**,
  from the ownership of the contexts), `kjOwnCoef` (**THE OWNERSHIP OF THE LAST COEFFICIENT**: below
  `ψ₂(β + W^{E+1})` every `v` has `v < ψ₂(β + W^E·v)`; `Kg.kgPlat` with `G(v) = β + ω^{Ω₂·E}·v`);
* `kjSucc` (the law at `(β + W^E·γ') + W^E`, the base `β + W^E·γ'` normal by the ownership),
  `kjLim` (the law at `β + W^E·γ` for a limit code `γ`, by the cofinal readings `Θc`, `c < γ`);
* `kjTop` (**THE TOP LAW AT EVERY NORMAL `β + W^E·γ`** with `W^{E+1} ∣ β`, by induction on the code `γ`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Zd Googology.Trans.PoR.InaccPsi.R2.Zx
  Googology.Trans.PoR.InaccPsi.R2.Zy Googology.Trans.PoR.InaccPsi.R2.Kc Googology.Trans.PoR.InaccPsi.R2.Kg
  Googology.Trans.PoR.InaccPsi.R2.Kh Googology.Trans.PoR.InaccPsi.R2.Ki Googology.Trans.PoR.InaccPsi.R2.Ka
  Googology.Trans.PoR.InaccPsi.R2.Xm

variable {S : InaccSeq.{0}}

/-- `kiX X₀ L + e` is a member once `X₀`, the components of `L` and `e` are. -/
theorem kjE_mem {a c e : Ordinal.{0}} (he : e ∈ S.CSet a c) : ∀ (L : List (Ordinal.{0} × Ordinal.{0})) (X₀ : Ordinal.{0}),
    X₀ ∈ S.CSet a c → (∀ p ∈ L, p.1 ∈ S.CSet a c ∧ p.2 ∈ S.CSet a c) → kiX X₀ L + e ∈ S.CSet a c
  | [], _, hX, _ => CSet.add_mem hX he
  | p :: L, X₀, hX, hc => kjE_mem he L (X₀ + leWe p.1 * p.2)
      (CSet.add_mem hX (leMulWe_mem (hc p List.mem_cons_self).1 (hc p List.mem_cons_self).2))
      (fun q hq => hc q (List.mem_cons_of_mem _ hq))

/-- **The components of `E = kiX X₀ L + e` lie below `ψ₂(β + W^E)`** once they lie below `ψ₂ M`,
`M ≤ β + W^{E+1}`. -/
theorem kjComp {l β e M : Ordinal.{0}} (he2 : e < Om (1 + 1)) :
    ∀ (L : List (Ordinal.{0} × Ordinal.{0})) (X₀ hb : Ordinal.{0}), KiValid S l hb L →
    M ≤ β + leWe (kiX X₀ L + e + 1) →
    (∀ p ∈ L, p.1 < S.psi M (Om (1 + 1)) ∧ p.2 < S.psi M (Om (1 + 1))) →
    ∀ p ∈ L, p.1 < S.psi (β + leWe (kiX X₀ L + e)) (Om (1 + 1)) ∧
      p.2 < S.psi (β + leWe (kiX X₀ L + e)) (Om (1 + 1))
  | [], _, _, _, _, _, _, hp => absurd hp List.not_mem_nil
  | p :: L, X₀, _, hv, hM, hcomp, q, hq => by
    have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
    obtain ⟨hc, h1, hθ, _, hζc, hζ0, hζθ, hvL⟩ := hv
    have hh2 : p.1 < Om (1 + 1) := hθ.trans (psi_lt hκ2 _)
    have hv' : KiValid S l (p.1 + 1) (p :: L) := ⟨hc, h1, hθ, lt_add_one _, hζc, hζ0, hζθ, hvL⟩
    have hE1 : kiX X₀ (p :: L) + e < X₀ + leWe (p.1 + 1) :=
      kiTail (p :: L) X₀ (p.1 + 1) e le_add_self hv' he2
    have hE2 : kiX X₀ (p :: L) + e < X₀ + leWe (Om (1 + 1)) :=
      hE1.trans_le (add_le_add le_rfl (leWe_mono (Order.add_one_le_of_lt hh2)))
    have hM1 : S.psi M (Om (1 + 1)) ≤ S.psi (β + leWe (X₀ + leWe (p.1 + 1))) (Om (1 + 1)) :=
      (psi_mono hκ2 (hM.trans (add_le_add le_rfl (leWe_mono (Order.add_one_le_of_lt hE1))))).1
    have hM2 : S.psi M (Om (1 + 1)) ≤ S.psi (β + leWe (X₀ + leWe (Om (1 + 1)))) (Om (1 + 1)) :=
      (psi_mono hκ2 (hM.trans (add_le_add le_rfl (leWe_mono (Order.add_one_le_of_lt hE2))))).1
    obtain ⟨hp1b, hp2b⟩ := hcomp p List.mem_cons_self
    -- the first use of `p.1` and of `p.2` lies below `E`
    have hfirst : X₀ + leWe p.1 * p.2 ≤ kiX X₀ (p :: L) + e := (kiX_ge L _).trans le_self_add
    have hfirst1 : X₀ + leWe p.1 ≤ kiX X₀ (p :: L) + e :=
      (add_le_add le_rfl (Ordinal.le_mul_left _ hζ0)).trans hfirst
    have hmid : p.1 < S.psi (β + leWe (X₀ + leWe p.1)) (Om (1 + 1)) := kgOwnExp p.1 (hp1b.trans_le hM2)
    rcases List.mem_cons.1 hq with rfl | hq'
    · refine ⟨hmid.trans_le (psi_mono hκ2 (add_le_add le_rfl (leWe_mono hfirst1))).1, ?_⟩
      exact (kgOwnBase (fun a c _ hq => CSet.of_lt hq) hmid q.2 (hp2b.trans_le hM1)).trans_le
        (psi_mono hκ2 (add_le_add le_rfl (leWe_mono hfirst))).1
    · exact kjComp he2 L (X₀ + leWe p.1 * p.2) p.1 hvL hM (fun r hr => hcomp r (List.mem_cons_of_mem _ hr)) q hq'

/-- **THE OWNERSHIP OF THE LAST COEFFICIENT**: below `ψ₂(β + W^{E+1})` every `v` has `v < ψ₂(β + W^E·v)`, once `E`
is a member of every closure `Cl(a, c)` with `ψ₂(β + W^E) ≤ c`. -/
theorem kjOwnCoef {β E : Ordinal.{0}}
    (hEm : ∀ a c : Ordinal.{0}, S.psi (β + leWe E) (Om (1 + 1)) ≤ c → E ∈ S.CSet a c) :
    ∀ v, v < S.psi (β + leWe (E + 1)) (Om (1 + 1)) → v < S.psi (β + leWe E * v) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set G : Ordinal.{0} → Ordinal.{0} := fun v => β + leWe E * v with hGdef
  have hGmono : Monotone G := fun _ _ h => add_le_add le_rfl (leMulWe_mono h)
  have h1 : (1 : Ordinal.{0}) ≤ kgX S (Om (1 + 1)) G 1 1 := by
    rw [kgX_succ, kgX_zero]; exact Order.one_le_iff_pos.2 (SC_psi hκ2 _).1
  have hx0 : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  have hmono : Monotone (kgX S (Om (1 + 1)) G 1) := monotone_nat_of_le_succ (kgX_mono hκ2 hGmono h1)
  have hfun : G = (KaT.base β (Om (1 + 1) * E)).ev := by funext v; rfl
  have hplat := kgPlat (S := S) (κ := Om (1 + 1)) (G := G) (x0 := 1) hκ2 hGmono h1 hx0
    (fun a b => mxOm2_mem a b) (fun n => by
      have hGn : β + leWe E ≤ G (kgX S (Om (1 + 1)) G 1 n) := by
        have h1n : (1 : Ordinal.{0}) ≤ kgX S (Om (1 + 1)) G 1 n := (le_refl 1).trans (hmono (Nat.zero_le n))
        exact add_le_add le_rfl (Ordinal.le_mul_left (leWe E) (zero_lt_one.trans_le h1n))
      have hEn : E ∈ S.CSet (G (kgX S (Om (1 + 1)) G 1 n)) (S.psi (G (kgX S (Om (1 + 1)) G 1 n)) (Om (1 + 1))) :=
        hEm _ _ (psi_mono hκ2 hGn).1
      have h := KaT.gapK (S := S) hκ2 (KaT.base β (Om (1 + 1) * E)) (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) hEn)
      rw [← hfun, ← kgX_succ] at h
      exact h)
  -- the ownership along the iterates
  have hown : ∀ n, ∀ v, v < kgX S (Om (1 + 1)) G 1 n → v < S.psi (G v) (Om (1 + 1)) := by
    intro n
    induction n with
    | zero =>
      intro v hv
      rw [kgX_zero] at hv
      rw [Order.lt_one_iff.1 hv]
      exact (SC_psi hκ2 _).1
    | succ n ih =>
      intro v hv
      rcases lt_or_ge v (kgX S (Om (1 + 1)) G 1 n) with h | h
      · exact ih v h
      · rw [kgX_succ] at hv
        exact hv.trans_le (psi_mono hκ2 (hGmono h)).1
  have hlt : ∀ n, kgX S (Om (1 + 1)) G 1 n < Om (1 + 1) := fun n => by
    cases n with
    | zero => exact hx0
    | succ n => rw [kgX_succ]; exact psi_lt hκ2 _
  have hbdd : BddAbove (range (kgX S (Om (1 + 1)) G 1)) := ⟨Om (1 + 1), by rintro _ ⟨n, rfl⟩; exact (hlt n).le⟩
  have hGΩ : G (Om (1 + 1)) = β + leWe (E + 1) := by simp only [hGdef]; rw [leWe_succ]
  intro v hv
  rw [← hGΩ] at hv
  obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 (hv.trans_le hplat)
  exact hown n v hn

/-- `E` and `γ` are members once `β + W^E·γ` is (`W^{E+1} ∣ β`, `0 < γ < Ω₂`). -/
theorem kjEfrom {a c β E γ : Ordinal.{0}} (hdv : leWe (E + 1) ∣ β) (hγ0 : γ ≠ 0) (hγ2 : γ < Om (1 + 1))
    (hb : β + leWe E * γ ∈ S.CSet a c) : E ∈ S.CSet a c ∧ γ ∈ S.CSet a c := by
  have hlt : leWe E * γ < leWe (E + 1) := by rw [leWe_succ]; exact mul_lt_mul_of_pos_left hγ2 (leWe_pos E)
  have h1 := (Vh.vhC_div _ hb (Om (1 + 1) * (E + 1))).2.1
  have e1 : (β + leWe E * γ) % ω ^ (Om (1 + 1) * (E + 1)) = leWe E * γ := by
    show (β + leWe E * γ) % leWe (E + 1) = leWe E * γ
    obtain ⟨q, hq⟩ := hdv
    rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hlt]
  rw [e1] at h1
  have hE := khh_mem hγ0 hγ2 h1
  exact ⟨hE, khζ_mem hE h1⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- **The law at `(β + W^E·γ') + W^E`** (`β` normal, `W^{E+1} ∣ β`, the components of `E` below `ψ₂(β + W^E)`,
`γ' < ψ₂(β + W^E·γ')`). -/
theorem kjSucc (k : ℕ) (L : List (Ordinal.{0} × Ordinal.{0})) (hv : KiValid S l (Om (1 + 1)) L)
    {β e γ' : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (he2 : e < Om (1 + 1)) (hβD : VbD S l β)
    (hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
    (hdv : leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e + 1) ∣ β)
    (hED : VbD S l (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e))
    (hEcomp : ∀ p ∈ L, p.1 < S.psi (β + leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e)) (Om (1 + 1)) ∧
      p.2 < S.psi (β + leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e)) (Om (1 + 1)))
    (heE : e < S.psi (β + leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e)) (Om (1 + 1)))
    (hγc : GxCl (upsilon l) (ldAtR S l) γ') (hγθ : γ' < ConjT.th S)
    (hγown : γ' < S.psi (β + leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e) * γ') (Om (1 + 1))) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e) * γ' +
      leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e)) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l (β + leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e) * γ' +
        leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e))) (Om (1 + 1))) (Om 1) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set X₀ := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hX₀def
  set X := kiX X₀ L with hXdef
  set E := X + e with hEdef
  set β' := β + leWe E * γ' with hβ'def
  have hγ2 : γ' < Om (1 + 1) := hγθ.trans (psi_lt hκ2 _)
  have hγH : γ' ∈ cdHull S l := (ldHull_iff hl hX hγ2).2 hγc
  have hEm : ∀ a c : Ordinal.{0}, S.psi (β + leWe E) (Om (1 + 1)) ≤ c → E ∈ S.CSet a c := fun a c hc =>
    kjE_mem (CSet.of_lt (heE.trans_le hc)) L X₀ (Vn.vnOmK3_mem k a c)
      (fun p hp => ⟨CSet.of_lt ((hEcomp p hp).1.trans_le hc), CSet.of_lt ((hEcomp p hp).2.trans_le hc)⟩)
  have hE1W : E + 1 < Om ω := vkOmW.1.isSuccLimit.add_one_lt hED.2.2
  have hWE1 : leWe (E + 1) < Om ω := (leWe_lt_SC vkOmW.1 vkOmW.2 hE1W).1
  have hWγ : leWe E * γ' < leWe (E + 1) := by
    rw [leWe_succ]; exact mul_lt_mul_of_pos_left hγ2 (leWe_pos E)
  have hβ'D : VbD S l β' :=
    ⟨CSet.add_mem hβD.1 (leMulWe_mem hED.1 hγH), CSet.add_mem hβD.2.1 (leMulWe_mem hED.2.1 (CSet.of_lt hγθ)),
      vkOmW.1.isPrincipal hβD.2.2 (hWγ.trans hWE1)⟩
  obtain ⟨hWED, -⟩ := zxTW hl hX hED
  have hbD' : VbD S l (β' + leWe E) :=
    ⟨CSet.add_mem hβ'D.1 hWED.1, CSet.add_mem hβ'D.2.1 hWED.2.1, vkOmW.1.isPrincipal hβ'D.2.2 hWED.2.2⟩
  -- `β'` is normal
  have hβ'n : β' ∈ S.CSet β' (S.psi β' (Om (1 + 1))) := by
    rcases eq_or_ne γ' 0 with h0 | h0
    · rw [hβ'def, h0, mul_zero, add_zero]; exact hβn
    · have hle : β + leWe E ≤ β' := add_le_add le_rfl (Ordinal.le_mul_left _ (pos_iff_ne_zero.2 h0))
      exact CSet.add_mem ((psi_mono hκ2 le_self_add).2 hβn)
        (leMulWe_mem (hEm _ _ (psi_mono hκ2 hle).1) (CSet.of_lt hγown))
  have hββ' : β + leWe E ≤ β' + leWe E := add_le_add le_self_add le_rfl
  have hcomp' : ∀ p ∈ L, p.1 < S.psi (β' + leWe E) (Om (1 + 1)) ∧ p.2 < S.psi (β' + leWe E) (Om (1 + 1)) :=
    fun p hp => ⟨(hEcomp p hp).1.trans_le (psi_mono hκ2 hββ').1, (hEcomp p hp).2.trans_le (psi_mono hκ2 hββ').1⟩
  have hKiQ : KiQ S l X₀ (fun _ => True) L β' :=
    kiCondM (M := β' + leWe E) he2 L X₀ (Om (1 + 1)) (fun _ => True) hv
      (add_le_add le_rfl (leWe_mono (le_of_lt (lt_add_one E)))) hcomp' trivial
  have heb' : e < S.psi (β' + leWe E) (Om (1 + 1)) := heE.trans_le (psi_mono hκ2 hββ').1
  have hdvβ' : leWe E ∣ β' := dvd_add ((leWe_dvd (le_of_lt (lt_add_one E))).trans hdv) (dvd_mul_right _ _)
  have hB : Ro.RoBaseE S l X e β' := by
    refine ⟨hdvβ', hβ'D.1, hbD'.2.2.trans_le (ConjT.OmW_le_A S _), fun d _ => (psi_mono hκ2 le_self_add).2 hβ'n,
      fun e' _ hle => ?_⟩
    have h0 := kgOwnBase (S := S) (β := β') (g₀ := X) (j := 0) (qj := 0) (fun a c _ _ => CSet.zero_mem a c)
      (SC_psi hκ2 _).1 e' (by
        rw [zero_add, leWe_one]
        exact (hle.trans_lt heb').trans_le (psi_mono hκ2 (add_le_add le_rfl (leWe_mono
          (add_le_add le_rfl he2.le)))).1)
    rwa [leWe_zero, one_mul] at h0
  have hlaw := kiChain hl hX hA hρ L (Om (1 + 1)) ((zdSh_Om hl hX (S := S) k).toQ (leRho hl hX).1.1)
    (fun _ => True) (fun _ _ => (SC_psi hκ2 _).1) (fun _ _ _ _ => trivial)
    (fun e hec he2 β hβD hB _ => xmTopUp S k l ηx A hl hX hA hρ e β hec he2 hβD hB) hv e hec he2 β' hβ'D hB hKiQ
  unfold ZdLaw leTe at hlaw
  exact hlaw

/-- **The law at `β + W^E·γ` for a limit code `γ`**, from the laws at `β + W^E·c` for the codes `0 < c < γ`. -/
theorem kjLim {β E γ : Ordinal.{0}} (hβD : VbD S l β) (hED : VbD S l E) (hγc : GxCl (upsilon l) (ldAtR S l) γ)
    (hγθ : γ < ConjT.th S) (hlim : IsSuccLimit γ)
    (IH : ∀ c, GxCl (upsilon l) (ldAtR S l) c → 0 < c → c < γ →
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe E * c) (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (vbT S l (β + leWe E * c)) (Om (1 + 1))) (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe E * γ) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l (β + leWe E * γ)) (Om (1 + 1))) (Om 1) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h0c : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero hρSC.1
  have hγ2 : γ < Om (1 + 1) := hγθ.trans (psi_lt hκ2 _)
  have hE1W : E + 1 < Om ω := vkOmW.1.isSuccLimit.add_one_lt hED.2.2
  have hWE1 : leWe (E + 1) < Om ω := (leWe_lt_SC vkOmW.1 vkOmW.2 hE1W).1
  -- `T(β + W^E·c) = Tβ + Ω^{TE}·Θc`, `β + W^E·c ∈ D`, for the codes `c ≤ γ`
  have hTc : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c ≤ γ → VbD S l (β + leWe E * c) ∧
      vbT S l (β + leWe E * c) = vbT S l β + leOe (vbT S l E) * gxTh (upsilon l) (ldAtR S l) c := by
    intro c hc hcγ
    have hc2 : c < Om (1 + 1) := hcγ.trans_lt hγ2
    have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hc2).2 hc
    have hcθ : c < ConjT.th S := hcγ.trans_lt hγθ
    have hWc : leWe E * c < leWe (E + 1) := by rw [leWe_succ]; exact mul_lt_mul_of_pos_left hc2 (leWe_pos E)
    have hWcD : VbD S l (leWe E * c) :=
      ⟨leMulWe_mem hED.1 hcH, leMulWe_mem hED.2.1 (CSet.of_lt hcθ), hWc.trans hWE1⟩
    refine ⟨⟨CSet.add_mem hβD.1 hWcD.1, CSet.add_mem hβD.2.1 hWcD.2.1, vkOmW.1.isPrincipal hβD.2.2 hWcD.2.2⟩, ?_⟩
    have h := Vh.vhT_cnfW hl hX hED (Xi.xiD_zero l) hcH hc2
    rw [add_zero, Vh.vhT_zero hl hX, add_zero] at h
    rw [Vh.vhT_add hl hX hβD hWcD, h]
  obtain ⟨hD, hT⟩ := hTc γ hγc le_rfl
  have hup := Xd.xdUp_at hl hX hA hρ _ hD
  rw [hT]
  rw [hT] at hup
  refine le_antisymm hup ?_
  have hγ0 : (0 : Ordinal.{0}) < γ := pos_iff_ne_zero.2 hlim.ne_bot
  have hΘ0 : 0 < gxTh (upsilon l) (ldAtR S l) γ := by
    have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) h0c hγ0; rwa [gxTh_zero] at this
  have hΘs := xmTh_lim hl hX hγ2 hlim
  have hΘlim : IsSuccLimit (gxTh (upsilon l) (ldAtR S l) γ) :=
    ⟨not_isMin_of_lt hΘ0, isSuccPrelimit_of_succ_lt fun a ha => by rw [Order.succ_eq_add_one]; exact hΘs a ha⟩
  have hOE : 0 < leOe (vbT S l E) := opow_pos _ omega0_pos
  set L := vbT S l β + leOe (vbT S l E) * gxTh (upsilon l) (ldAtR S l) γ with hLdef
  have hLlim : IsSuccLimit L := isSuccLimit_add _ (isSuccLimit_mul_right hOE hΘlim)
  set P := S.psi L (Om (1 + 1)) with hPdef
  have hPSC : SC P := SC_psi hκ2 _
  have hlimP : IsSuccLimit (A + 1 + P) := isSuccLimit_add _ hPSC.isSuccLimit
  -- the readings of the codes below `γ`
  have hread : ∀ c, GxCl (upsilon l) (ldAtR S l) c → 0 < c → c < γ →
      S.psi (A + 1 + S.psi (vbT S l β + leOe (vbT S l E) * gxTh (upsilon l) (ldAtR S l) c) (Om (1 + 1))) (Om 1) ≤
        gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe E * γ) (Om (1 + 1))) := by
    intro c hc hc0 hcγ
    have hlw := IH c hc hc0 hcγ
    rw [(hTc c hc hcγ.le).2] at hlw
    rw [← hlw]
    exact gxTh_mono (psi_mono hκ2 (add_le_add le_rfl (leMulWe_mono hcγ.le))).1
  have h1c : GxCl (upsilon l) (ldAtR S l) 1 := GxCl.small (gg_one_lt_of_SC hρSC)
  have h1γ : (1 : Ordinal.{0}) < γ := by have := hlim.add_one_lt hγ0; rwa [zero_add] at this
  have hr0 := hread 1 h1c zero_lt_one h1γ
  rw [Lw.lw_psi_limit S hκ1 hlimP]
  refine ciSup_le' fun ξ => ?_
  rcases lt_or_ge ξ.1 (A + 1) with h1 | h1
  · exact (psi_mono (S := S) hκ1 (h1.le.trans le_self_add)).1.trans hr0
  · have ee : ξ.1 = A + 1 + (ξ.1 - (A + 1)) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt' : ξ.1 - (A + 1) < P := Ry.rySub_lt h1 ξ.2
    have hlt2 : ξ.1 - (A + 1) < ⨆ z : Iio L, S.psi z.1 (Om (1 + 1)) :=
      lt_of_lt_of_eq hlt' (Lw.lw_psi_limit S hκ2 hLlim)
    have hbdd : BddAbove (range fun z : Iio L => S.psi z.1 (Om (1 + 1))) :=
      ⟨Om (1 + 1), by rintro _ ⟨z, rfl⟩; exact (psi_lt hκ2 _).le⟩
    haveI : Nonempty (Iio L) := ⟨⟨0, hLlim.bot_lt⟩⟩
    obtain ⟨z, hz⟩ := (lt_ciSup_iff hbdd).1 hlt2
    -- `z < Tβ + Ω^{TE}·Θγ` gives `z < Tβ + Ω^{TE}·Θc` for a code `0 < c < γ`
    obtain ⟨c, hc, hc0, hcγ, hzc⟩ : ∃ c, GxCl (upsilon l) (ldAtR S l) c ∧ 0 < c ∧ c < γ ∧
        z.1 < vbT S l β + leOe (vbT S l E) * gxTh (upsilon l) (ldAtR S l) c := by
      rcases lt_or_ge z.1 (vbT S l β) with hz1 | hz1
      · refine ⟨1, h1c, zero_lt_one, h1γ, hz1.trans_le le_self_add⟩
      · have hsub : z.1 - vbT S l β < leOe (vbT S l E) * gxTh (upsilon l) (ldAtR S l) γ := Ry.rySub_lt hz1 z.2
        set t := (z.1 - vbT S l β) / leOe (vbT S l E) with ht
        have htγ : t < gxTh (upsilon l) (ldAtR S l) γ := (Ordinal.lt_mul_iff_div_lt hOE.ne').1 hsub
        obtain ⟨c, hc, hcγ, hct⟩ := gxTh_onto (hΘs t htγ)
        have hc0 : 0 < c := by
          rcases eq_or_ne c 0 with h0 | h0
          · exfalso; rw [h0, gxTh_zero] at hct; exact absurd hct.symm (lt_of_le_of_lt zero_le (lt_add_one t)).ne'
          · exact pos_iff_ne_zero.2 h0
        refine ⟨c, hc, hc0, hcγ, ?_⟩
        have hzz : z.1 = vbT S l β + (z.1 - vbT S l β) := (Ordinal.add_sub_cancel_of_le hz1).symm
        rw [hzz, hct]
        have := Ordinal.lt_mul_succ_div (z.1 - vbT S l β) hOE.ne'
        rw [Order.succ_eq_add_one] at this
        exact (add_lt_add_iff_left _).2 this
    have h2 := hread c hc hc0 hcγ
    rw [ee]
    exact (psi_mono hκ1 (add_le_add le_rfl (hz.le.trans (psi_mono hκ2 hzc.le).1))).1.trans h2

/-- **THE TOP LAW AT EVERY NORMAL `b = β + W^E·γ`**, `E = Ω_{k+3} + W-polynomial + e`, `W^{E+1} ∣ β`, `γ` a code
with `0 < γ < θ`. -/
theorem kjTop (k : ℕ) (L : List (Ordinal.{0} × Ordinal.{0})) (hv : KiValid S l (Om (1 + 1)) L)
    {β e γ : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (he2 : e < Om (1 + 1)) (hβD : VbD S l β)
    (hdv : leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e + 1) ∣ β)
    (hγc : GxCl (upsilon l) (ldAtR S l) γ) (hγ0 : 0 < γ) (hγθ : γ < ConjT.th S)
    (hbD : VbD S l (β + leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e) * γ))
    (hbn : β + leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e) * γ ∈
      S.CSet (β + leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e) * γ)
        (S.psi (β + leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e) * γ) (Om (1 + 1)))) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e) * γ)
      (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l (β + leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e) * γ))
        (Om (1 + 1))) (Om 1) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set X₀ := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hX₀def
  set X := kiX X₀ L with hXdef
  set E := X + e with hEdef
  set b := β + leWe E * γ with hbdef
  have hγ2 : γ < Om (1 + 1) := hγθ.trans (psi_lt hκ2 _)
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt hκ2 _
  -- divisibilities
  have hX₀W : leWe X₀ = X₀ := Vn.vnWe_OmK k
  have hΩX₀ : Om (1 + 1) ≤ X₀ := Om_le_Om.2 (by
    calc (1 + 1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 + 1 := by simp [add_assoc]
      _ ≤ (k : Ordinal.{0}) + 1 + 1 + 1 := le_self_add)
  have hdvX₀ : leWe (Om (1 + 1)) ∣ X₀ := by have := leWe_dvd hΩX₀; rwa [hX₀W] at this
  have hdv1X₀ : leWe 1 ∣ X₀ := (leWe_dvd (gg_one_lt_of_SC ldOm2_SC).le).trans hdvX₀
  have hge := kiValid_ge L (Om (1 + 1)) hv
  have hΩ2X : Om (1 + 1) ∣ X := by
    have h := kiDvd L X₀ (Om (1 + 1)) 1 hv hdv1X₀ (fun p hp => (hge p hp).1)
    rwa [leWe_one] at h
  -- the components lie below `ψ₂(b)`
  have hEγ := kjEfrom hdv hγ0.ne' hγ2 hbn
  have hEm0 := hEγ.1
  have hem := khe_mem hΩ2X he2 hEm0
  have hXm := khX_mem hΩ2X he2 hEm0
  have hcomp := kiExtract L X₀ (Om (1 + 1)) hv hdvX₀ hXm
  have hbounds : ∀ p ∈ L, p.1 < S.psi b (Om (1 + 1)) ∧ p.2 < S.psi b (Om (1 + 1)) := fun p hp =>
    ⟨lt_psi_of_mem hκ2 (hcomp p hp).1 ((kiValid_mem L _ hv p hp).1.trans hθ2),
      lt_psi_of_mem hκ2 (hcomp p hp).2 ((kiValid_mem L _ hv p hp).2.trans hθ2)⟩
  have heb : e < S.psi b (Om (1 + 1)) := lt_psi_of_mem hκ2 hem he2
  have hγb : γ < S.psi b (Om (1 + 1)) := lt_psi_of_mem hκ2 hEγ.2 hγ2
  -- `E ∈ D`
  have hED : VbD S l E := by
    refine ⟨(kjEfrom hdv hγ0.ne' hγ2 hbD.1).1, (kjEfrom hdv hγ0.ne' hγ2 hbD.2.1).1, ?_⟩
    refine lt_of_le_of_lt ?_ hbD.2.2
    refine ((Ordinal.right_le_opow E one_lt_omega0).trans (opow_le_opow_right omega0_pos
      (Ordinal.le_mul_right E ldOm2_SC.1))).trans ?_
    exact (Ordinal.le_mul_left (leWe E) hγ0).trans le_add_self
  -- `β` is normal
  have hbW1 : b ≤ β + leWe (E + 1) := by
    rw [leWe_succ]; exact add_le_add le_rfl (leMulWe_mono hγ2.le)
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by
    have h := Zp.zpPreO_norm hκ2 (Om (1 + 1) * (E + 1)) hbn
    have hlt : leWe E * γ < leWe (E + 1) := by rw [leWe_succ]; exact mul_lt_mul_of_pos_left hγ2 (leWe_pos E)
    have e1 : ω ^ (Om (1 + 1) * (E + 1)) * (b / ω ^ (Om (1 + 1) * (E + 1))) = β := by
      obtain ⟨q, hq⟩ := hdv
      show leWe (E + 1) * (b / leWe (E + 1)) = β
      rw [hbdef, hq, Ordinal.mul_add_div _ (leWe_pos _).ne', Ordinal.div_eq_zero_of_lt hlt, add_zero]
    rwa [e1] at h
  -- the components of `E` lie below `ψ₂(β + W^E)`
  have hEcomp := kjComp (S := S) (β := β) (M := b) he2 L X₀ (Om (1 + 1)) hv hbW1 hbounds
  have heE : e < S.psi (β + leWe E) (Om (1 + 1)) := by
    have h0 := kgOwnBase (S := S) (β := β) (g₀ := X) (j := 0) (qj := 0) (fun a c _ _ => CSet.zero_mem a c)
      (SC_psi hκ2 _).1 e (by
        rw [zero_add, leWe_one]
        exact heb.trans_le (psi_mono hκ2 (hbW1.trans (add_le_add le_rfl (leWe_mono
          (Order.add_one_le_of_lt ((add_lt_add_iff_left X).2 he2)))))).1)
    rwa [leWe_zero, one_mul] at h0
  have hEm : ∀ a c : Ordinal.{0}, S.psi (β + leWe E) (Om (1 + 1)) ≤ c → E ∈ S.CSet a c := fun a c hc =>
    kjE_mem (CSet.of_lt (heE.trans_le hc)) L X₀ (Vn.vnOmK3_mem k a c)
      (fun p hp => ⟨CSet.of_lt ((hEcomp p hp).1.trans_le hc), CSet.of_lt ((hEcomp p hp).2.trans_le hc)⟩)
  have hown := kjOwnCoef (S := S) hEm
  have hγW : γ < S.psi (β + leWe (E + 1)) (Om (1 + 1)) := hγb.trans_le (psi_mono hκ2 hbW1).1
  -- induction on the coefficient
  have hall : ∀ c, GxCl (upsilon l) (ldAtR S l) c → 0 < c → c ≤ γ →
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe E * c) (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (vbT S l (β + leWe E * c)) (Om (1 + 1))) (Om 1) := by
    intro c
    induction c using WellFoundedLT.induction with
    | ind c IHc =>
    intro hc hc0 hcγ
    rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨c', hc'⟩ | hlimc
    · exact absurd h0 hc0.ne'
    · rw [succ_eq_add_one] at hc'
      subst hc'
      have hc2 : c' + 1 < Om (1 + 1) := hcγ.trans_lt hγ2
      have hc'c : GxCl (upsilon l) (ldAtR S l) c' :=
        (ldHull_iff hl hX ((lt_add_one c').trans hc2)).1 (mem_of_add_one_mem ((ldHull_iff hl hX hc2).2 hc))
      have hc'θ : c' < ConjT.th S := ((lt_add_one c').trans_le hcγ).trans hγθ
      have hc'own : c' < S.psi (β + leWe E * c') (Om (1 + 1)) :=
        hown c' (((lt_add_one c').trans_le hcγ).trans hγW)
      have e1 : β + leWe E * (c' + 1) = β + leWe E * c' + leWe E := by rw [mul_add_one, add_assoc]
      rw [e1]
      exact kjSucc hl hX hA hρ k L hv hec he2 hβD hβn hdv hED hEcomp heE hc'c hc'θ hc'own
    · exact kjLim hl hX hA hρ hβD hED hc (hcγ.trans_lt hγθ) hlimc fun c' hc'c hc'0 hc'lt =>
        IHc c' hc'lt hc'c hc'0 (hc'lt.le.trans hcγ)
  exact hall γ hγc hγ0 le_rfl

end Main

end Googology.Trans.PoR.InaccPsi.R2.Kj

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kj.kjOwnCoef
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kj.kjComp
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kj.kjSucc
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kj.kjTop
