import Googology.Trans.PoR.InaccPsi.R2.RxBlk

/-!
# The normal argument of a collapse in `HCl` stays in `HCl`

`HCl S α β` is `Cl(α, β)` without the countable collapses (`Bt.HCl`), `M = InaccSeq.M` (`M_{e,g}(x)`: the least
member of `Cl(e, g)` at or above `x`), `MGood`, `MQ` as in the notation's `NFM` (the principal summands of `x`,
and of every `q0(c, x)`, are in the target together with their `M`).

The notation proves `arg_mem_of_psi_mem` (`ψ_κ(d) ∈ Cl(α, β)`, `β ≤ ψ_κ(d)`, `d` in its own closure `⇒ d ∈ Cl(α, β)`,
`d < α`) through target sets closed under every collapse.  `HCl S α β` is not closed under `ψ_{Ω₁}`, but `M` never
makes a countable collapse when `g > Ω₁` (every countable ordinal is below `g`), so the same proof runs with:

* `RxClosed S e T` (**closed target sets without the countable collapses**: `Closed` with `ψ_{Ω_{s+1}}` only for
  `s ≠ 0`), `rxClosed_HCl` (`HCl S α β` is one for `e ≤ α`);
* `rxM_mem_of_Good`, `rxMQ_SC`, `rxMQ_mem`, `rxMQ_small`, `rxMQ_phi`, `rxMQ_Om`, `rxMQ_psiS` (`s ≠ 0`), `rxMQ_psiI`
  (the one-step lemmas of `NFM` for `RxClosed` targets);
* `rxMQ_of_mem_HCl` (**every member of `HCl S α β` satisfies `MQ`** for `R = Cl(e, g)`, `e ≤ α`, `β ≤ g`);
* `rxPrin_HCl` (the principal members of `HCl S α β` at or above `β`);
* `rxArgH` (**THE NORMAL ARGUMENT IN `HCl`**: `ψ_κ(d) ∈ HCl S α β`, `β ≤ ψ_κ(d)`, `d ∈ Cl(d, ψ_κ(d))` give
  `d ∈ HCl S α β` and `d < α`);
* `rxTh_nf_H` (**the atoms below `θ` in `HCl`**: `ψ_{Ω₂}(b) < θ` in `HCl S a Z` with `Z ≤ ψ_{Ω₂}(b)` is
  `ψ_{Ω₂}(d)` with `d < Ω_ω`, `d < a`, `d ∈ HCl S a Z`, `d ∈ Cl(d, ψ_{Ω₂}(d))`, `d ∈ Cl(Ω_ω, ψ_{Ω₂}(d))`; the
  `HCl` form of `Ry.ryTh_nf_mem`).

No new axiom.  New definition: `RxClosed` (a structure of closure conditions).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt

/-- **Closed target sets without the countable collapses.** -/
structure RxClosed (S : InaccSeq.{0}) (e : Ordinal.{0}) (T : Set Ordinal.{0}) : Prop where
  zero : (0 : Ordinal.{0}) ∈ T
  I : ∀ n, S.I n ∈ T
  add : ∀ x y, x ∈ T → y ∈ T → x + y ∈ T
  phi : ∀ x y, x ∈ T → y ∈ T → veblen x y ∈ T
  om : ∀ x, x ∈ T → Om x ∈ T
  psiS : ∀ s w, s ≠ 0 → s ∈ T → w ∈ T → w < e → S.psi w (Om (s + 1)) ∈ T
  psiI : ∀ n w, w ∈ T → w < e → S.psi w (S.I n) ∈ T
  lt : ∀ x ∈ T, x < S.Lam

variable {S : InaccSeq.{0}} {e g : Ordinal.{0}} {T : Set Ordinal.{0}}

theorem RxClosed.one_mem (hT : RxClosed S e T) : (1 : Ordinal.{0}) ∈ T := by
  have := hT.phi 0 0 hT.zero hT.zero
  rwa [veblen_zero_apply, opow_zero] at this

theorem rxMGood_one (hT : RxClosed S e T) : MGood S e g T 1 := by
  intro h hc
  rw [show (1 : Ordinal.{0}) = ω ^ (0 : Ordinal.{0}) from (opow_zero ω).symm] at hc
  rw [hc.eq_of_opow, opow_zero, M_eq_self (CSet.one_mem e g)]
  exact ⟨hT.one_mem, hT.one_mem⟩

theorem rxMGood_succ (hT : RxClosed S e T) {a : Ordinal.{0}} (ha : MGood S e g T a) :
    MGood S e g T (a + 1) := MGood_add ha (rxMGood_one hT)

theorem rx_mem_of_Good (hT : RxClosed S e T) {x : Ordinal.{0}} (hx : MGood S e g T x) : x ∈ T :=
  mem_of_comps hT.zero hT.add x fun h hc => (hx h hc).1

/-- **`M(x) ∈ T` when `x` is `MGood`** (the proof of `M_mem_of_Good`, which uses only `0` and `+`). -/
theorem rxM_mem_of_Good (hT : RxClosed S e T) :
    ∀ x : Ordinal.{0}, x < S.Lam → MGood S e g T x → S.M e g x ∈ T := by
  intro x
  induction x using WellFoundedLT.induction with
  | _ x IH =>
    intro hx hcomp
    by_cases hx0 : x = 0
    · subst hx0
      rw [M_eq_self (CSet.zero_mem e g)]
      exact hT.zero
    set h := Ordinal.log ω x with hh
    have hpS := hcomp h (comp_lead hx0)
    have hr : tail x < x := tail_lt hx0
    have hMr : S.M e g (tail x) ∈ T :=
      IH _ hr (lt_trans hr hx) (fun h' hc => hcomp h' (Comp.of_tail hx0 hc))
    obtain ⟨hMxR, hxMx⟩ := M_spec (e := e) (g := g) hx
    by_cases hpR : (ω : Ordinal.{0}) ^ h ∈ S.CSet e g
    · obtain ⟨hMrR, hrMr⟩ := M_spec (e := e) (g := g) (lt_trans hr hx)
      have hsum : S.M e g x = ω ^ h + S.M e g (tail x) := by
        refine le_antisymm (M_le (CSet.add_mem hpR hMrR) ?_) ?_
        · conv_lhs => rw [← lead_add_tail hx0]
          exact (add_le_add_iff_left _).2 hrMr
        · have hpm : (ω : Ordinal.{0}) ^ h ≤ S.M e g x := le_trans (lead_le hx0) hxMx
          have hm0 : S.M e g x ≠ 0 :=
            ne_of_gt (lt_of_lt_of_le (Ordinal.opow_pos _ omega0_pos) hpm)
          have hlog : h ≤ Ordinal.log ω (S.M e g x) :=
            Ordinal.le_log_of_opow_le Ordinal.one_lt_omega0 hpm
          rcases eq_or_lt_of_le hlog with hl | hl
          · have hlead : lead (S.M e g x) = ω ^ h := by rw [lead, ← hl]
            have htR := (lead_tail_mem hMxR hm0).2
            have hdec := lead_add_tail hm0
            rw [hlead] at hdec
            have hrt : tail x ≤ tail (S.M e g x) := by
              have h1 : ω ^ h + tail x ≤ ω ^ h + tail (S.M e g x) := by
                rw [hdec]
                conv_lhs => rw [show (ω : Ordinal.{0}) ^ h = lead x from rfl, lead_add_tail hx0]
                exact hxMx
              exact (add_le_add_iff_left _).1 h1
            conv_rhs => rw [← hdec]
            exact (add_le_add_iff_left _).2 (M_le htR hrt)
          · have hbig : (ω : Ordinal.{0}) ^ (h + 1) ≤ S.M e g x :=
              le_trans (Ordinal.opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hl))
                (lead_le hm0)
            refine le_trans (le_of_lt ?_) hbig
            have hne : h + 1 ≠ 0 := (add_pos_of_right zero_lt_one h).ne'
            obtain ⟨e', he', n, hn⟩ := (Ordinal.lt_omega0_opow hne).1 (tail_lt_opow x)
            have hle : (ω : Ordinal.{0}) ^ e' * n ≤ ω ^ h * n :=
              mul_le_mul_left
                (Ordinal.opow_le_opow_right omega0_pos (Order.lt_add_one_iff.1 he')) _
            have hMrle : S.M e g (tail x) ≤ ω ^ h * n :=
              M_le (mul_nat_mem hpR n) (le_of_lt (lt_of_lt_of_le hn hle))
            refine Ordinal.isPrincipal_add_omega0_opow (h + 1) (opow_lt_opow_add_one h) ?_
            exact lt_of_le_of_lt hMrle (Ordinal.omega0_opow_mul_nat_lt (lt_add_one h) n)
      rw [hsum]
      exact hT.add _ _ hpS.1 hMr
    · obtain ⟨hMpR, hpMp⟩ := M_spec (e := e) (g := g)
        (lt_of_le_of_lt (lead_le hx0) hx : (ω : Ordinal.{0}) ^ h < S.Lam)
      have heq : S.M e g x = S.M e g (ω ^ h) := by
        refine le_antisymm (M_le hMpR ?_) (M_le hMxR (le_trans (lead_le hx0) hxMx))
        exact le_trans (le_of_lt (lt_opow_log_add_one x))
          (opow_add_one_le_of_notMem hpR hMpR hpMp)
      rw [heq]
      exact hpS.2

theorem rxMQ_SC (hT : RxClosed S e T) {x : Ordinal.{0}} (hSC : SC x) (hxT : x ∈ T)
    (hMT : S.M e g x ∈ T) : MQ S e g T x := by
  have G : MGood S e g T x := MGood_prin hSC.isPrincipal hSC.1.ne' hxT hMT
  refine ⟨G, fun c => ?_⟩
  rcases q0_SC hSC c with h | h | h <;> rw [h]
  · exact MGood_zero
  · exact rxMGood_one hT
  · exact rxMGood_succ hT G

theorem rxMQ_mem (hT : RxClosed S e T) {x : Ordinal.{0}} (hSC : SC x) (hxR : x ∈ S.CSet e g)
    (hxT : x ∈ T) : MQ S e g T x :=
  rxMQ_SC hT hSC hxT (by rw [M_eq_self hxR]; exact hxT)

theorem rxMQ_small (hT : RxClosed S e T) {x : Ordinal.{0}} (hxg : x < g)
    (hall : ∀ z ≤ x, z ∈ T) : MQ S e g T x := by
  have G : MGood S e g T x := MGood_small hxg hall
  refine ⟨G, fun c => ?_⟩
  rcases (q0_le_add_one c x).lt_or_eq with h | h
  · have h' := Order.lt_add_one_iff.1 h
    exact MGood_small (lt_of_le_of_lt h' hxg) fun z hz => hall z (hz.trans h')
  · rw [h]; exact rxMGood_succ hT G

theorem rxMQ_phi (hT : RxClosed S e T) {a b : Ordinal.{0}} (ha : MQ S e g T a)
    (hb : MQ S e g T b) : MQ S e g T (veblen a b) := by
  have haT := rx_mem_of_Good hT ha.1
  have hbT := rx_mem_of_Good hT hb.1
  have hxT := hT.phi a b haT hbT
  have hxL := hT.lt _ hxT
  by_cases hxa : veblen a b = a
  · rw [hxa]; exact ha
  by_cases hxb : veblen a b = b
  · rw [hxb]; exact hb
  have hal : a < veblen a b := lt_of_le_of_ne (left_le_veblen a b) (Ne.symm hxa)
  have hbl : b < veblen a b := lt_of_le_of_ne (right_le_veblen a b) (Ne.symm hxb)
  have hMT : S.M e g (veblen a b) ∈ T := by
    by_cases hR : veblen a b ∈ S.CSet e g
    · rw [M_eq_self hR]; exact hxT
    by_cases haR : a ∈ S.CSet e g
    · rw [M_veblen_of_mem hxL hR hbl haR]
      exact hT.phi _ _ haT (rxM_mem_of_Good hT b (hT.lt _ hbT) hb.1)
    · rw [M_veblen_of_notMem hxL hR hal hbl haR]
      have hMa := rxM_mem_of_Good hT a (hT.lt _ haT) ha.1
      exact hT.phi _ _ hMa (rxM_mem_of_Good hT _
        (lt_of_le_of_lt (q0_le_add_one _ _) (add_one_lt_Lam (hT.lt _ hbT))) (hb.2 _))
  have G : MGood S e g T (veblen a b) :=
    MGood_prin (veblen_isPrincipal a b) veblen_pos.ne' hxT hMT
  refine ⟨G, fun c => ?_⟩
  rcases q0_veblen c a b with h | h | h <;> rw [h]
  · exact hb.2 c
  · exact rxMGood_succ hT hb.1
  · exact rxMGood_succ hT G

theorem rxMQ_Om (hT : RxClosed S e T) {a : Ordinal.{0}} (ha : MQ S e g T a) :
    MQ S e g T (Om a) := by
  by_cases ha0 : a = 0
  · rw [ha0, Om_zero]; exact MQ_zero
  have haT := rx_mem_of_Good hT ha.1
  have haL := hT.lt _ haT
  refine rxMQ_SC hT (SC_Om ha0) (hT.om _ haT) ?_
  rw [M_Om haL]
  exact hT.om _ (rxM_mem_of_Good hT a haL ha.1)

theorem rxMQ_psiS (hT : RxClosed S e T) {s y : Ordinal.{0}} (hs0 : s ≠ 0) (hs : MGood S e g T s)
    (hy : MGood S e g T y) (hxT : S.psi y (Om (s + 1)) ∈ T) :
    MQ S e g T (S.psi y (Om (s + 1))) := by
  have hsT := rx_mem_of_Good hT hs
  have hyT := rx_mem_of_Good hT hy
  have hsL := hT.lt _ hsT
  have hyL := hT.lt _ hyT
  refine rxMQ_SC hT (SC_psi (InR_Om_succ s) y) hxT ?_
  by_cases hR : S.psi y (Om (s + 1)) ∈ S.CSet e g
  · rw [M_eq_self hR]; exact hxT
  rcases M_psiS hyL hsL hR with h | h | ⟨hlt, h⟩ <;> rw [h]
  · exact hT.om _ (hT.add _ _ hsT hT.one_mem)
  · exact hT.om _ (rxM_mem_of_Good hT s hsL hs)
  · exact hT.psiS s _ hs0 hsT (rxM_mem_of_Good hT y hyL hy) hlt

theorem rxMQ_psiI (hT : RxClosed S e T) {n : ℕ} {y : Ordinal.{0}} (hy : MGood S e g T y)
    (hxT : S.psi y (S.I n) ∈ T) : MQ S e g T (S.psi y (S.I n)) := by
  have hyT := rx_mem_of_Good hT hy
  have hyL := hT.lt _ hyT
  refine rxMQ_SC hT (SC_psi (InR_I n) y) hxT ?_
  by_cases hR : S.psi y (S.I n) ∈ S.CSet e g
  · rw [M_eq_self hR]; exact hxT
  rcases M_psiI hyL hR with h | ⟨hlt, h⟩ <;> rw [h]
  · exact hT.I n
  · exact hT.psiI n _ (rxM_mem_of_Good hT y hyL hy) hlt

theorem rxI_ne_Om1 (n : ℕ) : S.I n ≠ Om 1 := (Gg.gg_Om1_lt_I S n).ne'

/-- **`HCl S α β` is a closed target set** for `e ≤ α`. -/
theorem rxClosed_HCl {α β : Ordinal.{0}} (heα : e ≤ α) (hβL : β ≤ S.Lam) :
    RxClosed S e {x | HCl S α β x} where
  zero := HCl.zero
  I := fun n => HCl.inacc n
  add := fun _ _ hx hy => HCl.add hx hy
  phi := fun _ _ hx hy => HCl.phi hx hy
  om := fun _ hx => HCl.om hx
  psiS := fun s _ hs0 hs hw hwe => HCl.coll (InR_Om_succ s)
    (fun h => hs0 (by have h' : s < 1 := (Om_inj.1 h) ▸ lt_add_one s; exact Order.lt_one_iff.1 h'))
    (HCl.om (HCl.succ hs)) hw (lt_of_lt_of_le hwe heα)
  psiI := fun n _ hw hwe => HCl.coll (InR_I n) (rxI_ne_Om1 n) (HCl.inacc n) hw (lt_of_lt_of_le hwe heα)
  lt := fun _ hx => lt_Lam_of_mem hβL (HCl.mem_CSet hx)

/-- **Every member of `HCl S α β` satisfies `MQ`**, for `R = Cl(e, g)` with `e ≤ α`, `β ≤ g`. -/
theorem rxMQ_of_mem_HCl {α β x : Ordinal.{0}} (heα : e ≤ α) (hβg : β ≤ g) (hβL : β ≤ S.Lam)
    (hx : HCl S α β x) :
    MQ S e g {x | HCl S α β x} x ∧ ∀ σ, x = Om σ → MGood S e g {x | HCl S α β x} σ := by
  have hT := rxClosed_HCl (S := S) (α := α) (β := β) heα hβL
  have Om0 : ∀ σ : Ordinal.{0}, 0 = Om σ → σ = 0 := fun σ hσ => by
    by_contra h; exact (Om_pos h).ne' hσ.symm
  induction hx with
  | @small y h =>
    have hall : ∀ z ≤ y, z ∈ {x | HCl S α β x} := fun z hz => HCl.small (lt_of_le_of_lt hz h)
    refine ⟨rxMQ_small hT (lt_of_lt_of_le h hβg) hall, fun σ hσ => ?_⟩
    have hσy : σ ≤ y := hσ ▸ le_Om σ
    exact MGood_small (lt_of_le_of_lt hσy (lt_of_lt_of_le h hβg))
      fun z hz => hall z (hz.trans hσy)
  | zero =>
    exact ⟨MQ_zero, fun σ hσ => by rw [Om0 σ hσ]; exact MGood_zero⟩
  | inacc n =>
    have Q := rxMQ_mem hT (SC_I n) (CSet.I_mem e g n) (HCl.inacc n)
    refine ⟨Q, fun σ hσ => ?_⟩
    rw [← Om_inj.1 ((Om_I n).trans hσ)]; exact Q.1
  | inaccW =>
    have Q := rxMQ_mem hT SC_Iw (CSet.Iw_mem e g) (HCl.inaccW (S := S) (a := α) (Z := β))
    refine ⟨Q, fun σ hσ => ?_⟩
    rw [← Om_inj.1 (S.Om_Iw.trans hσ)]; exact Q.1
  | @add p q _ _ ihp ihq =>
    refine ⟨MQ_add ihp.1 ihq.1, fun σ hσ => ?_⟩
    by_cases hσ0 : σ = 0
    · rw [hσ0]; exact MGood_zero
    by_cases hq0 : q = 0
    · rw [hq0, add_zero] at hσ; exact ihp.2 σ hσ
    have hpz : p < p + q := lt_add_of_pos_right p (pos_iff_ne_zero.2 hq0)
    have hP := (SC_Om hσ0).isPrincipal
    rw [hσ] at hpz
    have hqz : q = Om σ := le_antisymm (hσ ▸ le_add_self)
      (not_lt.1 fun h => absurd hσ (hP hpz h).ne)
    exact ihq.2 σ hqz
  | @phi p q _ _ ihp ihq =>
    refine ⟨rxMQ_phi hT ihp.1 ihq.1, fun σ hσ => ?_⟩
    by_cases hσ0 : σ = 0
    · rw [hσ0, Om_zero] at hσ; exact absurd hσ veblen_pos.ne'
    rcases (SC_Om hσ0).eq_of_veblen_eq hσ with h | h
    · exact ihp.2 σ h
    · exact ihq.2 σ h
  | @om p _ ihp =>
    refine ⟨rxMQ_Om hT ihp.1, fun σ hσ => ?_⟩
    rw [← Om_inj.1 hσ]; exact ihp.1.1
  | @coll π e' hπ hπ1 hπC heC hea ihπ ihe =>
    rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
    · have Q := rxMQ_psiI hT ihe.1.1 (HCl.coll (InR_I n) hπ1 hπC heC hea)
      refine ⟨Q, fun σ hσ => ?_⟩
      have : σ = S.psi e' (S.I n) := Om_inj.1 (hσ.symm.trans (Om_psiI e' n).symm)
      rw [this]; exact Q.1
    · have hs1 := ihπ.2 (s + 1) rfl
      have hs : MGood S e g {x | HCl S α β x} s := fun h hc => hs1 h hc.add_one
      have hs0 : s ≠ 0 := fun h0 => hπ1 (by rw [h0, zero_add])
      have Q := rxMQ_psiS hT hs0 hs ihe.1.1 (HCl.coll (InR_Om_succ s) hπ1 hπC heC hea)
      exact ⟨Q, fun σ hσ =>
        absurd hσ (not_Om_of_between (psiS_bounds _ _).1 (psiS_bounds _ _).2 σ)⟩

/-- **The principal members of `HCl S a b` at or above `b`.** -/
theorem rxPrin_HCl {a b z : Ordinal.{0}} (hz : HCl S a b z) (hbz : b ≤ z)
    (hP : IsPrincipal (· + ·) z) (hz0 : z ≠ 0) :
    (∃ n, z = S.I n) ∨ z = S.Iw ∨
    (∃ p q, HCl S a b p ∧ HCl S a b q ∧ p < z ∧ q < z ∧ z = veblen p q) ∨
    (∃ p, HCl S a b p ∧ p < z ∧ z = Om p) ∨
    (∃ π e, S.InR π ∧ π ≠ Om 1 ∧ HCl S a b π ∧ HCl S a b e ∧ e < a ∧ z = S.psi e π) := by
  revert hbz hP hz0
  induction hz with
  | small h => intro hbz _ _; exact absurd (lt_of_lt_of_le h hbz) (lt_irrefl _)
  | zero => intro _ _ hz0; exact absurd rfl hz0
  | inacc n => intro _ _ _; exact Or.inl ⟨n, rfl⟩
  | inaccW => intro _ _ _; exact Or.inr (Or.inl rfl)
  | @add p q _ _ ihp ihq =>
    intro hbz hP hz0
    by_cases hq0 : q = 0
    · subst hq0
      simp only [add_zero] at hbz hP hz0 ⊢
      exact ihp hbz hP hz0
    · have hpz : p < p + q := lt_add_of_pos_right p (pos_iff_ne_zero.2 hq0)
      have hqz : q = p + q :=
        le_antisymm le_add_self (not_lt.1 fun h => lt_irrefl _ (hP hpz h))
      rw [← hqz] at hbz hP hz0 ⊢
      exact ihq hbz hP hz0
  | @phi p q hp hq ihp ihq =>
    intro hbz hP hz0
    by_cases hpz : p = veblen p q
    · rw [← hpz] at hbz hP hz0 ⊢; exact ihp hbz hP hz0
    by_cases hqz : q = veblen p q
    · rw [← hqz] at hbz hP hz0 ⊢; exact ihq hbz hP hz0
    exact Or.inr (Or.inr (Or.inl ⟨p, q, hp, hq, lt_of_le_of_ne (left_le_veblen p q) hpz,
      lt_of_le_of_ne (right_le_veblen p q) hqz, rfl⟩))
  | @om p hp ihp =>
    intro hbz hP hz0
    rcases (le_Om p).lt_or_eq with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, h, rfl⟩)))
    · rw [← h] at hbz hP hz0 ⊢; exact ihp hbz hP hz0
  | @coll π e hπ hπ1 hπC heC hea _ _ =>
    intro _ _ _
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨π, e, hπ, hπ1, hπC, heC, hea, rfl⟩)))

/-- **THE NORMAL ARGUMENT IN `HCl`**: `ψ_κ(d) ∈ HCl S α β`, `β ≤ ψ_κ(d)` and `d ∈ Cl(d, ψ_κ(d))` give
`d ∈ HCl S α β` and `d < α`. -/
theorem rxArgH {κ d α β : Ordinal.{0}} (hκ : S.InR κ)
    (hmem : HCl S α β (S.psi d κ)) (hβz : β ≤ S.psi d κ) (hβL : β ≤ S.Lam)
    (hd : d ∈ S.CSet d (S.psi d κ)) : HCl S α β d ∧ d < α := by
  have hdα : d < α := by
    by_contra hcon
    exact psi_notMem hκ d (CSet_mono (not_lt.1 hcon) hβz (HCl.mem_CSet hmem))
  refine ⟨?_, hdα⟩
  have hSC := SC_psi hκ d
  rcases rxPrin_HCl hmem hβz hSC.isPrincipal hSC.1.ne' with
    ⟨n, hn⟩ | hw | ⟨p, q, _, _, hp, hq, hpq⟩ | ⟨p, _, hp, hpz⟩ |
      ⟨π, e, hπ, _, _, heC, heα, hz⟩
  · exfalso
    rcases hκ with ⟨m, rfl⟩ | ⟨s, rfl⟩
    · have hnm : n < m := S.strictMono.lt_iff_lt.1 (hn ▸ psi_lt (InR_I m) d)
      have := I_lt_psiI_of_lt (S := S) d hnm
      rw [hn] at this; exact lt_irrefl _ this
    · exact not_Om_of_between (psiS_bounds d s).1 (psiS_bounds d s).2 (S.I n)
        (hn.trans (Om_I n).symm)
  · exfalso
    rcases hκ with ⟨m, rfl⟩ | ⟨s, rfl⟩
    · have := (psi_lt (S := S) (InR_I m) d).trans (S.I_lt_Iw m)
      rw [hw] at this; exact lt_irrefl _ this
    · exact not_Om_of_between (psiS_bounds d s).1 (psiS_bounds d s).2 S.Iw
        (hw.trans S.Om_Iw.symm)
  · exact absurd hpq.symm (hSC.not_veblen_lt hp hq)
  · exfalso
    rcases hκ with ⟨m, rfl⟩ | ⟨s, rfl⟩
    · have : S.psi d (S.I m) = p := Om_inj.1 ((Om_psiI d m).trans hpz)
      rw [this] at hp; exact lt_irrefl _ hp
    · exact not_Om_of_between (psiS_bounds d s).1 (psiS_bounds d s).2 p hpz
  · have hπκ : π = κ := sub_eq_of_psi_eq hπ hκ hz.symm
    subst hπκ
    have heL : e < S.Lam := lt_Lam_of_mem hβL (HCl.mem_CSet heC)
    have hg : S.psi e π = S.psi d π := hz.symm
    have hβg : β ≤ S.psi e π := hg ▸ hβz
    have hT := rxClosed_HCl (S := S) (e := e) (α := α) (β := β) heα.le hβL
    have hQ := (rxMQ_of_mem_HCl (e := e) (g := S.psi e π) heα.le hβg hβL heC).1
    have hMmem : HCl S α β (S.M e (S.psi e π) e) := rxM_mem_of_Good hT e heL hQ.1
    have hMd : S.M e (S.psi e π) e = d := by
      have h1 := M_mem_self hπ heL
      have h2 : S.psi (S.M e (S.psi e π) e) π = S.psi d π := (psi_M_eq hπ heL).trans hg
      have hc := compare_psi hπ h1 hd
      rw [h2, compare_eq_iff_eq.2 rfl] at hc
      exact compare_eq_iff_eq.1 hc.symm
    rw [← hMd]; exact hMmem

/-- **The atoms below `θ` in `HCl`**: the normal-form argument is in `HCl`, below `a` and below `Ω_ω`. -/
theorem rxTh_nf_H {b a Z : Ordinal.{0}} (hb : S.psi b (Om (1 + 1)) < ConjT.th S)
    (hmem : HCl S a Z (S.psi b (Om (1 + 1)))) (hZ : Z ≤ S.psi b (Om (1 + 1))) :
    ∃ d, d < Om ω ∧ d < a ∧ S.psi d (Om (1 + 1)) = S.psi b (Om (1 + 1)) ∧ HCl S a Z d ∧
      d ∈ S.CSet d (S.psi d (Om (1 + 1))) ∧ d ∈ S.CSet (Om ω) (S.psi d (Om (1 + 1))) := by
  obtain ⟨h1, h2, h3, h4⟩ := Ry.ryNf_spec (InR_Om_succ 1) Ry.ryOmW_mem hb
  have hκL : Om (1 + 1 : Ordinal.{0}) ≤ S.Lam := (lt_Lam_of_mem zero_le (Mx.mxOm2_mem (S := S) 0 0)).le
  have hZL : Z ≤ S.Lam := (hZ.trans (psi_lt (InR_Om_succ 1) _).le).trans hκL
  obtain ⟨h5, h6⟩ := rxArgH (InR_Om_succ 1) (by rw [h2]; exact hmem) (by rw [h2]; exact hZ) hZL h3
  exact ⟨_, h1, h6, h2, h5, h3, h4⟩

end Googology.Trans.PoR.InaccPsi.R2.Rx
