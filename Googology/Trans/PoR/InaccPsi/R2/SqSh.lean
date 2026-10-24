import Googology.Trans.PoR.InaccPsi.R2.SqLev

/-!
# The family with the shift `ε_{Ω₂+1}`: every atom below `ψ_{Ω₂}(W^{ε+Ω₂})` is own

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `ε = ε_{Ω₂+1}`, `ε̂ = ε_{Ω₁+1}`,
`F_ε = ψ_{Ω₂}(ε) = T_ε(0)`, `T_{ε+Ω₂}(0) = ψ_{Ω₂}(W^{ε+Ω₂}) = ψ_{Ω₂}(ε·W^{Ω₂})`.

`sqShE S λ b X X̂`: the family `Sn.snShG` (exponents below `ε`) together with the shift `(ε, ε̂)` at every base.

* `sqOwn_fam`, `sqCls_fam` (own arguments and `Rw.RwClsAt` are monotone in the family);
* `sqShE_mono`, `sqShE_sh` (**every member is a shift own relative to its base with the top law at every code
  `e`**: the new member by `Sq.sqSh_eps`, `Sq.sqLev_eps`, `Rv.rvTopE`);
* `sqCls_eps0` (**the atoms below `T_ε(β)` are own at every base `β` with a reading**: `Rw.rwClsLimSh` with the
  members `W^{t_k}`, `t_k` the tower, and `Sn.snClsLev_all`), `sqCls_epsE` (every code `e`, `Rw.rwClsE`),
  `sqCls_epsW` (**`T_{ε+Ω₂}(β)`**, `Rw.rwClsW`);
* `sqRepE` (**every atom `s < T_{ε+Ω₂}(0)` is `≤ ψ_{Ω₂}(0)` or `ψ_{Ω₂}(c)` with `c` own over `0`** for `sqShE`),
  `sqReadE` (**`Θ(ψ_{Ω₂}(c)) = ψ_{Ω₁}(A + 1 + v)`** for those), `sqRead_Feps` (**`Θ(ψ_{Ω₂}(ε)) = ψ_{Ω₁}(A+1+ε̂)`**).

No new axiom.  New definition: the family `sqShE`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg
  Googology.Trans.PoR.InaccPsi.R2.Sn

variable {S : InaccSeq.{0}}

/-- **The family `snShG` with the shift `(ε, ε̂)`.** -/
def sqShE (S : InaccSeq.{0}) (l b X Xh : Ordinal.{0}) : Prop :=
  snShG S l b X Xh ∨ (X = veblen 1 (Om (1 + 1) + 1) ∧ Xh = veblen 1 (Om 1 + 1))

/-- Own arguments are monotone in the family. -/
theorem sqOwn_fam {l : Ordinal.{0}} {Sh Sh' : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop}
    (hS : ∀ b X Xh, Sh b X Xh → Sh' b X Xh) {X e β c v : Ordinal.{0}} (h : RwOwn S l Sh X e β c v) :
    RwOwn S l Sh' X e β c v := by
  induction h with
  | low h => exact RwOwn.low h
  | succ hsh hec hγc hγ0 hγT hcond _ ih => exact RwOwn.succ (hS _ _ _ hsh) hec hγc hγ0 hγT hcond ih

theorem sqCls_fam {l : Ordinal.{0}} {Sh Sh' : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop}
    (hS : ∀ b X Xh, Sh b X Xh → Sh' b X Xh) {X e β : Ordinal.{0}} (h : RwClsAt S l Sh X e β) :
    RwClsAt S l Sh' X e β := by
  intro t ht htT
  rcases h t ht htT with h | ⟨X', e', c, v, hc, ho, hb, e1⟩
  · exact Or.inl h
  · exact Or.inr ⟨X', e', c, v, hc, sqOwn_fam hS ho, hb, e1⟩

theorem sqShE_mono {l b b' X Xh : Ordinal.{0}} (hbb : b ≤ b') (h : sqShE S l b X Xh) : sqShE S l b' X Xh := by
  rcases h with h | h
  · exact Or.inl (snShG_mono hbb h)
  · exact Or.inr h

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- `ε + Ω₂ < ψ_{Ω₃}(0)` and `ε̂ + Ω₁ < ψ_{Ω₂}(0)` (the bounds of the offset `0`). -/
theorem sqEps_bounds :
    0 + leWe (veblen 1 (Om (1 + 1) + 1)) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) ∧
      0 + leOe (veblen 1 (Om 1 + 1)) + Om 1 < S.psi 0 (Om (1 + 1)) := by
  rw [zero_add, zero_add, sqEps_We, sqEpsH_Oe]
  exact ⟨rwG3_SC.isPrincipal snEps_lt_G3 rwW_lt_G3, rwG_SC.isPrincipal sqEpsH_lt_G rwO_lt_G⟩

/-- **The shift `ε` (image `ε̂`) is own relative to every base, with the top law at every code `e`.** -/
theorem sqShEps (b : Ordinal.{0}) : RvSh S l b (veblen 1 (Om (1 + 1) + 1)) (veblen 1 (Om 1 + 1)) ∧
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
      RvTop S l b (veblen 1 (Om (1 + 1) + 1)) (veblen 1 (Om 1 + 1)) e := by
  obtain ⟨hG3, hG⟩ := sqEps_bounds (S := S) hl hX
  have hoff : RvOff S l b 0 0 := Or.inl ⟨rfl, rfl⟩
  have hs := sqSh_eps hl hX hoff hG3 hG
  have ht := sqLev_eps hl hX b 0 0 hoff (dvd_zero _) hG3 hG trivial
  rw [zero_add, zero_add, sqEps_We, sqEpsH_Oe] at hs ht
  exact ⟨hs, rvTopE hs hl hX ht⟩

/-- **Every member of `sqShE` is a shift own relative to its base with the top law at every code.** -/
theorem sqShE_sh : ∀ b X Xh, sqShE S l b X Xh → RvSh S l b X Xh ∧
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → RvTop S l b X Xh e := by
  rintro b X Xh (h | ⟨rfl, rfl⟩)
  · exact snShG_sh hl hX b X Xh h
  · exact sqShEps hl hX b

/-- **The atoms below `T_ε(β)` are own** (family `sqShE`) at every base `β` with a reading. -/
theorem sqCls_eps0 (β : Ordinal.{0}) :
    RoBaseE S l (veblen 1 (Om (1 + 1) + 1)) 0 β → RwRd S l β →
      RwClsAt S l (sqShE S l) (veblen 1 (Om (1 + 1) + 1)) 0 β := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  refine rwClsLimSh hl hX (sqShE_sh hl hX) ?_
  intro x _ hx
  obtain ⟨k, hk⟩ := sqTw_cof ldOm2_SC hx
  have hE1 : 1 ≤ sqTw (Om (1 + 1)) k := sqOne_le_tw ldOm2_SC k
  have hEε : sqTw (Om (1 + 1)) k < veblen 1 (Om (1 + 1) + 1) := sqTw_lt ldOm2_SC k
  have hEH : sqTw (Om (1 + 1)) k ∈ cdHull S l := sqTwW_mem k
  have hG : SnG S l β (leWe (sqTw (Om (1 + 1)) k) * 1)
      (leOe (sgThH S l (sqTw (Om (1 + 1)) k)) * gxTh (upsilon l) (ldAtR S l) 1) (sqTw (Om (1 + 1)) k) :=
    SnG.one hE1 hEH hEε (fun Q hQ _ => sqTw_cl ldOm2_SC hQ k) (GxCl.small (gg_one_lt_of_SC hρSC)) one_ne_zero
      ⟨0, show (1 : Ordinal.{0}) < Om 1 from sqOne_lt_Om1⟩
  rw [mul_one] at hG
  have hWε : leWe (sqTw (Om (1 + 1)) k) < veblen 1 (Om (1 + 1) + 1) := sqTw_lt ldOm2_SC (k + 1)
  refine ⟨_, _, Or.inl ⟨_, hG⟩, (Ph.ph_veblen_prin 1 _ hWε sqK_lt_eps).le,
    hk.trans (sqTw_lt_succ ldOm2_SC k), fun hb hrd => ?_⟩
  have hcl : SnCL S (sqTw (Om (1 + 1)) k) 0 0 := fun Q hQ _ => sqTw_cl ldOm2_SC hQ k
  have h := snClsLev_all hl hX _ hEH hE1 hEε 0 0 0 (Or.inl ⟨rfl, rfl⟩) hcl β zero_le
    (by rwa [zero_add]) hrd
  rw [zero_add] at h
  exact sqCls_fam (fun _ _ _ h => Or.inl h) h

/-- **The atoms below `T_{ε+e}(β)` are own** for every code `e`, at every base with a reading. -/
theorem sqCls_epsE : ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β,
    RoBaseE S l (veblen 1 (Om (1 + 1) + 1)) e β → RwRd S l β →
      RwClsAt S l (sqShE S l) (veblen 1 (Om (1 + 1) + 1)) e β := by
  intro e hec heW β hb hrd
  exact rwClsE hl hX (sqShE_sh hl hX) (fun _ _ _ _ h1 h2 => sqShE_mono h1 h2) (b := 0)
    (Or.inr ⟨rfl, rfl⟩) (fun β _ hb hrd => sqCls_eps0 hl hX β hb hrd) e hec heW β zero_le hb hrd

/-- **The atoms below `T_{ε+Ω₂}(β)` are own** at every base with a reading. -/
theorem sqCls_epsW (β : Ordinal.{0}) :
    RoBaseE S l (veblen 1 (Om (1 + 1) + 1) + Om (1 + 1)) 0 β → RwRd S l β →
      RwClsAt S l (sqShE S l) (veblen 1 (Om (1 + 1) + 1) + Om (1 + 1)) 0 β :=
  rwClsW hl hX (sqShE_sh hl hX) (fun _ _ _ _ h1 h2 => sqShE_mono h1 h2) (b := 0) (Or.inr ⟨rfl, rfl⟩)
    (fun e hec heW β _ hb hrd => sqCls_epsE hl hX e hec heW β hb hrd) β zero_le

/-- `ε + Ω₂ < Ω_ω`. -/
theorem sqEpsW_lt_OmW : veblen 1 (Om (1 + 1) + 1) + Om (1 + 1) < Om (ω : Ordinal.{0}) :=
  rwX_W (Or.inr ⟨_, (sqShEps (S := S) hl hX 0).1⟩)

/-- **Every atom `s < T_{ε+Ω₂}(0)` is `≤ ψ_{Ω₂}(0)` or `ψ_{Ω₂}(c)` with `c` own over `0`** (family `sqShE`). -/
theorem sqRepE {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l)
    (hsT : s < leTe S (veblen 1 (Om (1 + 1) + 1) + Om (1 + 1)) 0) :
    s ≤ S.psi 0 (Om (1 + 1)) ∨ ∃ X e c v, (X = 0 ∨ ∃ Xh, sqShE S l 0 X Xh) ∧
      RwOwn S l (sqShE S l) X e 0 c v ∧ RoBaseE S l X e 0 ∧ s = S.psi c (Om (1 + 1)) := by
  have hb : RoBaseE S l (veblen 1 (Om (1 + 1) + 1) + Om (1 + 1)) 0 0 := by
    refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
    · rw [zero_add, add_zero]
      exact (roWe_lt_OmW (sqEpsW_lt_OmW hl hX)).trans_le le_self_add
    · obtain rfl : e' = 0 := le_antisymm h' zero_le
      exact (SC_psi (InR_Om_succ 1) _).1
  have hcls := sqCls_epsW hl hX 0 hb (rwRd_zero (S := S) (l := l) hA hρ)
  have htT : s < leTe S (veblen 1 (Om (1 + 1) + 1) + Om (1 + 1) + 0) 0 := by rw [add_zero]; exact hsT
  rcases hcls _ hs htT with h | ⟨X', e', c, v, -, hown, hbo, e1⟩
  · exact Or.inl h
  · rw [zero_add] at e1
    exact Or.inr ⟨X', e', c, v, rwOwn_sh hown, hown, hbo, e1⟩

/-- **`Θ_λ(ψ_{Ω₂}(c)) = ψ_{Ω₁}(A + 1 + v)`** for every own `(X, e, c, v)` over `0` (family `sqShE`). -/
theorem sqReadE {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {X e c v : Ordinal.{0}} (hown : RwOwn S l (sqShE S l) X e 0 c v) (hb : RoBaseE S l X e 0) :
    gxTh (upsilon l) (ldAtR S l) (S.psi c (Om (1 + 1))) = S.psi (A + 1 + v) (Om 1) ∧
      A + 1 + v ∈ S.CSet (A + 1 + v) (S.psi (A + 1 + v) (Om 1)) ∧ c < leWe (X + e) ∧
      v < S.psi 0 (Om (1 + 1)) := by
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  obtain ⟨e1, own1, hc, hv⟩ := rwOwnRead hl hX (sqShE_sh hl hX) hown (A + 1) hb hA1 (ldBlk_zero hA hρ)
  rw [zero_add] at e1
  exact ⟨e1, own1, hc, hv⟩

/-- The base `0` of the shift `ε`. -/
theorem sqBase0 : RoBaseE S l (veblen 1 (Om (1 + 1) + 1)) 0 0 :=
  rwBase0 (Or.inr ⟨_, (sqShEps hl hX 0).1⟩) (sqEpsW_lt_OmW hl hX)
    ((Om_pos one_ne_zero).trans (leOm1_lt_Te _ _))

/-- **`Θ_λ(ψ_{Ω₂}(ε_{Ω₂+1})) = ψ_{Ω₁}(A + 1 + ε_{Ω₁+1})`.** -/
theorem sqRead_Feps {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (veblen 1 (Om (1 + 1) + 1)) (Om (1 + 1))) =
      S.psi (A + 1 + veblen 1 (Om 1 + 1)) (Om 1) := by
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  have h := (sqShEps hl hX 0).2 0 (GxCl.zero (leRho hl hX).1.1) (ldOm2_SC.1) 0 (A + 1) (sqBase0 hl hX) le_rfl
    hA1 (ldBlk_zero hA hρ)
  rw [add_zero, gxTh_zero, add_zero, sqEpsH_Oe] at h
  unfold leTe at h
  rwa [zero_add, sqEps_We] at h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Sq
