import Googology.Trans.PoR.InaccPsi.R2.UlEq

/-!
# M-rounding keeps the visibility closure `K_q`: the normalized closure

`W = Ω_{s+1}`, `ψ_π = S.psi · π`, `K_q = Ul.UlK S s q` (the closure of `q ∪ {0, I_n, I_ω}` under `+`, `φ`, `Ω_·` and
every `ψ_π`, `π ≠ W`, with any argument), `M(e) = S.M e (ψ_π e) e` (the least member of `Cl(e, ψ_π e)` at or above
`e`; `InaccSeq.M_mem_self`, `InaccSeq.psi_M_eq`).  The library lemma `InaccSeq.M_mem_of_Good` asks a target set closed
under every collapse with argument below `e`; `K_q` is not closed under `ψ_W`.  Here the same argument is run for a
target that is closed under the collapses `ψ_π`, `π ≠ W` only, and the collapses `ψ_W(y) < q` of a member of `K_q`
are leaves below `q ≤ ψ_π(e)`, which `M` fixes:

* `UoK` (**the normalized closure**: as `K_q`, but a collapse `ψ_π(e)` is formed only at an argument `e` in its own
  closure `Cl(e, ψ_π(e))`), `UoK.toK`, `UoK.lt_Lam`;
* `UoCl` (the closure conditions of `InaccSeq.Closed` with the collapses `ψ_W` left out), `uoM_mem_of_Good` (the
  library `M_mem_of_Good` for it), `uoMQ_*`, `uoMQ_of` (**every member of `UoK` satisfies `MQ`** for `R = Cl(e, g)`,
  `q ≤ g`);
* `uo_norm` (**`ψ_π(ξ)` is in `UoK` for every `ξ ∈ UoK`, `π ≠ W`**: by induction on `ξ`, the argument is moved up to
  `M(ξ)`), `uoK_of_K` (**`K_q ⊆ UoK`**, so `K_q = UoK`), `uoM_mem` (**M-rounding keeps `K_q`**: `e ∈ K_q`,
  `q ≤ ψ_π(e)` give `M(e) ∈ K_q`), `uoArg` (**the K-version of `InaccSeq.arg_mem_of_psi_mem`**: the own
  argument `d` of a collapse `ψ_π(d) ∈ K_q`, `q ≤ ψ_π(d)`, is in `K_q`), `uoSub` (so is the subscript `π`).

No new axiom.  New definitions: `UoK`, `UoCl`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uo

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul

/-- **The normalized visibility closure**: as `K_q`, with every collapse `ψ_π(e)` (`π ≠ W`) formed at an argument `e`
in its own closure. -/
inductive UoK (S : InaccSeq.{0}) (s q : Ordinal.{0}) : Ordinal.{0} → Prop
  | small {x : Ordinal.{0}} : x < q → UoK S s q x
  | zero : UoK S s q 0
  | inacc (n : ℕ) : UoK S s q (S.I n)
  | inaccW : UoK S s q S.Iw
  | add {x y : Ordinal.{0}} : UoK S s q x → UoK S s q y → UoK S s q (x + y)
  | phi {x y : Ordinal.{0}} : UoK S s q x → UoK S s q y → UoK S s q (veblen x y)
  | om {x : Ordinal.{0}} : UoK S s q x → UoK S s q (Om x)
  | coll {π e : Ordinal.{0}} : S.InR π → π ≠ Om (s + 1) → UoK S s q π → UoK S s q e →
      e ∈ S.CSet e (S.psi e π) → UoK S s q (S.psi e π)

variable {S : InaccSeq.{0}} {s q : Ordinal.{0}}

theorem UoK.toK {x : Ordinal.{0}} (h : UoK S s q x) : UlK S s q x := by
  induction h with
  | small h => exact UlK.small h
  | zero => exact UlK.zero
  | inacc n => exact UlK.inacc n
  | inaccW => exact UlK.inaccW
  | add _ _ ihx ihy => exact UlK.add ihx ihy
  | phi _ _ ihx ihy => exact UlK.phi ihx ihy
  | om _ ih => exact UlK.om ih
  | coll hπ hπW _ _ _ ihπ ihe => exact UlK.coll hπ hπW ihπ ihe

theorem UoK.one : UoK S s q 1 := by
  have := UoK.phi (S := S) (s := s) (q := q) UoK.zero UoK.zero; rwa [veblen_zero_apply, opow_zero] at this

theorem UoK.lt_Lam (hqL : q ≤ S.Lam) {x : Ordinal.{0}} (h : UoK S s q x) : x < S.Lam := by
  induction h with
  | small h => exact h.trans_le hqL
  | zero => exact lt_of_le_of_lt zero_le one_lt_Lam
  | inacc n => exact I_lt_Lam n
  | inaccW => exact Iw_lt_Lam
  | add _ _ ihx ihy => exact add_lt_Lam ihx ihy
  | phi _ _ ihx ihy => exact veblen_lt_Lam ihx ihy
  | om _ ih => exact Om_lt_Lam ih
  | coll hπ _ _ _ _ ihπ _ => exact (psi_lt hπ _).trans ihπ

/-! ## Closure conditions without `ψ_W` -/

/-- The closure conditions of `InaccSeq.Closed`, with the collapses at the subscript `W` left out. -/
structure UoCl (S : InaccSeq.{0}) (W e : Ordinal.{0}) (T : Set Ordinal.{0}) : Prop where
  zero : (0 : Ordinal.{0}) ∈ T
  I : ∀ n, S.I n ∈ T
  add : ∀ x y, x ∈ T → y ∈ T → x + y ∈ T
  phi : ∀ x y, x ∈ T → y ∈ T → veblen x y ∈ T
  om : ∀ x, x ∈ T → Om x ∈ T
  psiS : ∀ t w, t ∈ T → w ∈ T → w < e → Om (t + 1) ≠ W → S.psi w (Om (t + 1)) ∈ T
  psiI : ∀ n w, w ∈ T → w < e → S.psi w (S.I n) ∈ T
  lt : ∀ x ∈ T, x < S.Lam

variable {W e g : Ordinal.{0}} {T : Set Ordinal.{0}}

theorem UoCl.one_mem (hT : UoCl S W e T) : (1 : Ordinal.{0}) ∈ T := by
  have := hT.phi 0 0 hT.zero hT.zero
  rwa [veblen_zero_apply, opow_zero] at this

theorem uoMGood_one (hT : UoCl S W e T) : MGood S e g T 1 := by
  intro h hc
  rw [show (1 : Ordinal.{0}) = ω ^ (0 : Ordinal.{0}) from (opow_zero ω).symm] at hc
  rw [hc.eq_of_opow, opow_zero, M_eq_self (CSet.one_mem e g)]
  exact ⟨hT.one_mem, hT.one_mem⟩

theorem uoMGood_succ (hT : UoCl S W e T) {a : Ordinal.{0}} (ha : MGood S e g T a) :
    MGood S e g T (a + 1) := MGood_add ha (uoMGood_one hT)

theorem uo_mem_of_Good (hT : UoCl S W e T) {x : Ordinal.{0}} (hx : MGood S e g T x) : x ∈ T :=
  mem_of_comps hT.zero hT.add x fun h hc => (hx h hc).1

/-- **`M(x) ∈ T` when `x` is `MGood`** (the library `M_mem_of_Good`; only `0 ∈ T` and `+` are used). -/
theorem uoM_mem_of_Good (hT : UoCl S W e T) :
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

/-! ## The one-step lemmas for `MQ` -/

theorem uoMQ_SC (hT : UoCl S W e T) {x : Ordinal.{0}} (hSC : SC x) (hxT : x ∈ T)
    (hMT : S.M e g x ∈ T) : MQ S e g T x := by
  have G : MGood S e g T x := MGood_prin hSC.isPrincipal hSC.1.ne' hxT hMT
  refine ⟨G, fun c => ?_⟩
  rcases q0_SC hSC c with h | h | h <;> rw [h]
  · exact MGood_zero
  · exact uoMGood_one hT
  · exact uoMGood_succ hT G

theorem uoMQ_mem (hT : UoCl S W e T) {x : Ordinal.{0}} (hSC : SC x) (hxR : x ∈ S.CSet e g)
    (hxT : x ∈ T) : MQ S e g T x :=
  uoMQ_SC hT hSC hxT (by rw [M_eq_self hxR]; exact hxT)

theorem uoMQ_small (hT : UoCl S W e T) {x : Ordinal.{0}} (hxg : x < g)
    (hall : ∀ z ≤ x, z ∈ T) : MQ S e g T x := by
  have G : MGood S e g T x := MGood_small hxg hall
  refine ⟨G, fun c => ?_⟩
  rcases (q0_le_add_one c x).lt_or_eq with h | h
  · have h' := Order.lt_add_one_iff.1 h
    exact MGood_small (lt_of_le_of_lt h' hxg) fun z hz => hall z (hz.trans h')
  · rw [h]; exact uoMGood_succ hT G

theorem uoMQ_phi (hT : UoCl S W e T) {a b : Ordinal.{0}} (ha : MQ S e g T a)
    (hb : MQ S e g T b) : MQ S e g T (veblen a b) := by
  have haT := uo_mem_of_Good hT ha.1
  have hbT := uo_mem_of_Good hT hb.1
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
      exact hT.phi _ _ haT (uoM_mem_of_Good hT b (hT.lt _ hbT) hb.1)
    · rw [M_veblen_of_notMem hxL hR hal hbl haR]
      have hMa := uoM_mem_of_Good hT a (hT.lt _ haT) ha.1
      exact hT.phi _ _ hMa (uoM_mem_of_Good hT _
        (lt_of_le_of_lt (q0_le_add_one _ _) (add_one_lt_Lam (hT.lt _ hbT))) (hb.2 _))
  have G : MGood S e g T (veblen a b) :=
    MGood_prin (veblen_isPrincipal a b) veblen_pos.ne' hxT hMT
  refine ⟨G, fun c => ?_⟩
  rcases q0_veblen c a b with h | h | h <;> rw [h]
  · exact hb.2 c
  · exact uoMGood_succ hT hb.1
  · exact uoMGood_succ hT G

theorem uoMQ_Om (hT : UoCl S W e T) {a : Ordinal.{0}} (ha : MQ S e g T a) :
    MQ S e g T (Om a) := by
  by_cases ha0 : a = 0
  · rw [ha0, Om_zero]; exact MQ_zero
  have haT := uo_mem_of_Good hT ha.1
  have haL := hT.lt _ haT
  refine uoMQ_SC hT (SC_Om ha0) (hT.om _ haT) ?_
  rw [M_Om haL]
  exact hT.om _ (uoM_mem_of_Good hT a haL ha.1)

theorem uoMQ_psiS (hT : UoCl S W e T) {t y : Ordinal.{0}} (hs : MGood S e g T t)
    (hy : MGood S e g T y) (hW : Om (t + 1) ≠ W) (hxT : S.psi y (Om (t + 1)) ∈ T) :
    MQ S e g T (S.psi y (Om (t + 1))) := by
  have hsT := uo_mem_of_Good hT hs
  have hyT := uo_mem_of_Good hT hy
  have hsL := hT.lt _ hsT
  have hyL := hT.lt _ hyT
  refine uoMQ_SC hT (SC_psi (InR_Om_succ t) y) hxT ?_
  by_cases hR : S.psi y (Om (t + 1)) ∈ S.CSet e g
  · rw [M_eq_self hR]; exact hxT
  rcases M_psiS hyL hsL hR with h | h | ⟨hlt, h⟩ <;> rw [h]
  · exact hT.om _ (hT.add _ _ hsT hT.one_mem)
  · exact hT.om _ (uoM_mem_of_Good hT t hsL hs)
  · exact hT.psiS t _ hsT (uoM_mem_of_Good hT y hyL hy) hlt hW

theorem uoMQ_psiI (hT : UoCl S W e T) {n : ℕ} {y : Ordinal.{0}} (hy : MGood S e g T y)
    (hxT : S.psi y (S.I n) ∈ T) : MQ S e g T (S.psi y (S.I n)) := by
  have hyT := uo_mem_of_Good hT hy
  have hyL := hT.lt _ hyT
  refine uoMQ_SC hT (SC_psi (InR_I n) y) hxT ?_
  by_cases hR : S.psi y (S.I n) ∈ S.CSet e g
  · rw [M_eq_self hR]; exact hxT
  rcases M_psiI hyL hR with h | ⟨hlt, h⟩ <;> rw [h]
  · exact hT.I n
  · exact hT.psiI n _ (uoM_mem_of_Good hT y hyL hy) hlt

/-- **Every member of `UoK` satisfies `MQ`** for `R = Cl(e, g)` with `q ≤ g`, given the closure conditions without
`ψ_W` for `UoK` at `e`; the second half is carried for the subscripts `Ω_{t+1}`. -/
theorem uoMQ_of (hT : UoCl S (Om (s + 1)) e {x | UoK S s q x}) (hqg : q ≤ g) :
    ∀ x, UoK S s q x → MQ S e g {x | UoK S s q x} x ∧
      ∀ σ, x = Om σ → MGood S e g {x | UoK S s q x} σ := by
  have Om0 : ∀ σ : Ordinal.{0}, 0 = Om σ → σ = 0 := fun σ hσ => by
    by_contra h; exact (Om_pos h).ne' hσ.symm
  intro x hx
  induction hx with
  | @small y h =>
    have hall : ∀ z ≤ y, z ∈ {x | UoK S s q x} := fun z hz => UoK.small (lt_of_le_of_lt hz h)
    refine ⟨uoMQ_small hT (lt_of_lt_of_le h hqg) hall, fun σ hσ => ?_⟩
    have hσy : σ ≤ y := hσ ▸ le_Om σ
    exact MGood_small (lt_of_le_of_lt hσy (lt_of_lt_of_le h hqg)) fun z hz => hall z (hz.trans hσy)
  | zero => exact ⟨MQ_zero, fun σ hσ => by rw [Om0 σ hσ]; exact MGood_zero⟩
  | inacc n =>
    have Q := uoMQ_mem hT (SC_I n) (CSet.I_mem e g n) (UoK.inacc n)
    refine ⟨Q, fun σ hσ => ?_⟩
    rw [← Om_inj.1 ((Om_I n).trans hσ)]; exact Q.1
  | inaccW =>
    have Q := uoMQ_mem hT SC_Iw (CSet.Iw_mem e g) UoK.inaccW
    refine ⟨Q, fun σ hσ => ?_⟩
    rw [← Om_inj.1 (S.Om_Iw.trans hσ)]; exact Q.1
  | @add p r _ _ ihp ihr =>
    refine ⟨MQ_add ihp.1 ihr.1, fun σ hσ => ?_⟩
    by_cases hσ0 : σ = 0
    · rw [hσ0]; exact MGood_zero
    by_cases hr0 : r = 0
    · rw [hr0, add_zero] at hσ; exact ihp.2 σ hσ
    have hpz : p < p + r := lt_add_of_pos_right p (pos_iff_ne_zero.2 hr0)
    have hP := (SC_Om hσ0).isPrincipal
    rw [hσ] at hpz
    have hrz : r = Om σ := le_antisymm (hσ ▸ le_add_self)
      (not_lt.1 fun h => absurd hσ (hP hpz h).ne)
    exact ihr.2 σ hrz
  | @phi p r _ _ ihp ihr =>
    refine ⟨uoMQ_phi hT ihp.1 ihr.1, fun σ hσ => ?_⟩
    by_cases hσ0 : σ = 0
    · rw [hσ0, Om_zero] at hσ; exact absurd hσ veblen_pos.ne'
    rcases (SC_Om hσ0).eq_of_veblen_eq hσ with h | h
    · exact ihp.2 σ h
    · exact ihr.2 σ h
  | @om p _ ihp =>
    refine ⟨uoMQ_Om hT ihp.1, fun σ hσ => ?_⟩
    rw [← Om_inj.1 hσ]; exact ihp.1.1
  | @coll π e' hπ hπW hπK heK hown ihπ ihe =>
    have hxT : S.psi e' π ∈ {x | UoK S s q x} := UoK.coll hπ hπW hπK heK hown
    rcases hπ with ⟨n, rfl⟩ | ⟨t, rfl⟩
    · have Q := uoMQ_psiI hT ihe.1.1 hxT
      refine ⟨Q, fun σ hσ => ?_⟩
      have : σ = S.psi e' (S.I n) := Om_inj.1 (hσ.symm.trans (Om_psiI e' n).symm)
      rw [this]; exact Q.1
    · have hs1 := ihπ.2 (t + 1) rfl
      have hs : MGood S e g {x | UoK S s q x} t := fun h hc => hs1 h hc.add_one
      have Q := uoMQ_psiS hT hs ihe.1.1 hπW hxT
      exact ⟨Q, fun σ hσ =>
        absurd hσ (not_Om_of_between (psiS_bounds _ _).1 (psiS_bounds _ _).2 σ)⟩

/-! ## Normalization -/

theorem uo_I_ne_W (n : ℕ) : S.I n ≠ Om (s + 1) := by
  intro h
  have h1 : Om (Om (s + 1)) = Om (s + 1) := by rw [← h]; exact Om_I n
  exact Om_ne_add_one (s + 1) s (Om_inj.1 h1)

/-- **`ψ_π(ξ) ∈ UoK` for every `ξ ∈ UoK` and every subscript `π ≠ W` in `UoK`**: by induction on `ξ`; the argument
is moved up to `M(ξ)`, which stays in `UoK` (`uoMQ_of`, `uoM_mem_of_Good`) and lies in its own closure. -/
theorem uo_norm (hqL : q ≤ S.Lam) : ∀ ξ : Ordinal.{0}, UoK S s q ξ →
    ∀ π, S.InR π → π ≠ Om (s + 1) → UoK S s q π → UoK S s q (S.psi ξ π) := by
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
  intro hξ π hπ hπW hπK
  by_cases hsm : S.psi ξ π < q
  · exact UoK.small hsm
  have hqg : q ≤ S.psi ξ π := not_lt.1 hsm
  have hT : UoCl S (Om (s + 1)) ξ {x | UoK S s q x} :=
    { zero := UoK.zero
      I := UoK.inacc
      add := fun _ _ => UoK.add
      phi := fun _ _ => UoK.phi
      om := fun _ => UoK.om
      psiS := fun t w ht hw hwξ hne =>
        IH w hwξ hw (Om (t + 1)) (InR_Om_succ t) hne (UoK.om (UoK.add ht UoK.one))
      psiI := fun n w hw hwξ => IH w hwξ hw (S.I n) (InR_I n) (uo_I_ne_W n) (UoK.inacc n)
      lt := fun _ hx => UoK.lt_Lam hqL hx }
  have hL : ξ < S.Lam := UoK.lt_Lam hqL hξ
  have hQ := (uoMQ_of hT hqg ξ hξ).1
  have hM : UoK S s q (S.M ξ (S.psi ξ π) ξ) := uoM_mem_of_Good hT ξ hL hQ.1
  rw [← psi_M_eq hπ hL]
  exact UoK.coll hπ hπW hπK hM (M_mem_self hπ hL)

/-- **`K_q ⊆ UoK`** (so `K_q = UoK`): every member of `K_q` has a derivation whose collapses are at own arguments. -/
theorem uoK_of_K (hqL : q ≤ S.Lam) {x : Ordinal.{0}} (h : UlK S s q x) : UoK S s q x := by
  induction h with
  | small h => exact UoK.small h
  | zero => exact UoK.zero
  | inacc n => exact UoK.inacc n
  | inaccW => exact UoK.inaccW
  | add _ _ ihx ihy => exact UoK.add ihx ihy
  | phi _ _ ihx ihy => exact UoK.phi ihx ihy
  | om _ ih => exact UoK.om ih
  | @coll π e hπ hπW _ _ ihπ ihe => exact uo_norm hqL e ihe π hπ hπW ihπ

/-- **M-rounding keeps `K_q`**: for `ξ ∈ K_q` and any `π` with `q ≤ ψ_π(ξ)`, `q ≤ Λ`: `M(ξ) ∈ K_q`. -/
theorem uoM_mem (hqL : q ≤ S.Lam) {π ξ : Ordinal.{0}} (hξ : UlK S s q ξ) (hqg : q ≤ S.psi ξ π) :
    UlK S s q (S.M ξ (S.psi ξ π) ξ) := by
  have hT : UoCl S (Om (s + 1)) ξ {x | UoK S s q x} :=
    { zero := UoK.zero
      I := UoK.inacc
      add := fun _ _ => UoK.add
      phi := fun _ _ => UoK.phi
      om := fun _ => UoK.om
      psiS := fun t w ht hw _ hne =>
        uo_norm hqL w hw (Om (t + 1)) (InR_Om_succ t) hne (UoK.om (UoK.add ht UoK.one))
      psiI := fun n w hw _ => uo_norm hqL w hw (S.I n) (InR_I n) (uo_I_ne_W n) (UoK.inacc n)
      lt := fun _ hx => UoK.lt_Lam hqL hx }
  have hξU := uoK_of_K hqL hξ
  exact (uoM_mem_of_Good hT ξ (UoK.lt_Lam hqL hξU) (uoMQ_of hT hqg ξ hξU).1.1).toK

/-! ## The own argument of a collapse in `K_q` -/

theorem uo_psi_ne_I {π d : Ordinal.{0}} (hπ : S.InR π) (n : ℕ) : S.psi d π ≠ S.I n := by
  intro hn
  rcases hπ with ⟨m, rfl⟩ | ⟨t, rfl⟩
  · have hnm : n < m := S.strictMono.lt_iff_lt.1 (hn ▸ psi_lt (InR_I m) d)
    have := I_lt_psiI_of_lt (S := S) d hnm
    rw [hn] at this; exact lt_irrefl _ this
  · exact not_Om_of_between (psiS_bounds d t).1 (psiS_bounds d t).2 (S.I n) (hn.trans (Om_I n).symm)

theorem uo_psi_ne_Iw {π d : Ordinal.{0}} (hπ : S.InR π) : S.psi d π ≠ S.Iw := by
  intro hw
  rcases hπ with ⟨m, rfl⟩ | ⟨t, rfl⟩
  · have := (psi_lt (S := S) (InR_I m) d).trans (S.I_lt_Iw m)
    rw [hw] at this; exact lt_irrefl _ this
  · exact not_Om_of_between (psiS_bounds d t).1 (psiS_bounds d t).2 S.Iw (hw.trans S.Om_Iw.symm)

/-- **The own argument and the subscript of a collapse in `UoK`** (`q ≤ ψ_π(d)`) are in `UoK`. -/
theorem uoArgU {π d : Ordinal.{0}} (hπ : S.InR π) (hd : d ∈ S.CSet d (S.psi d π)) :
    ∀ z, UoK S s q z → z = S.psi d π → q ≤ z → UoK S s q d ∧ UoK S s q π := by
  have hSC := SC_psi hπ d
  intro z hz
  induction hz with
  | small h => intro hz hqz; exact absurd (h.trans_le hqz) (lt_irrefl _)
  | zero => intro hz _; exact absurd hz.symm hSC.1.ne'
  | inacc n => intro hz _; exact absurd hz.symm (uo_psi_ne_I hπ n)
  | inaccW => intro hz _; exact absurd hz.symm (uo_psi_ne_Iw hπ)
  | @add x y _ _ ihx ihy =>
    intro hz hqz
    by_cases hy0 : y = 0
    · subst hy0; rw [add_zero] at hz hqz; exact ihx hz hqz
    have hxz : x < x + y := lt_add_of_pos_right x (pos_iff_ne_zero.2 hy0)
    have hyz : y = x + y := by
      refine le_antisymm le_add_self (not_lt.1 fun h => ?_)
      rw [hz] at hxz h
      exact absurd hz (hSC.isPrincipal hxz h).ne
    rw [← hyz] at hz hqz; exact ihy hz hqz
  | @phi x y _ _ ihx ihy =>
    intro hz hqz
    rcases hSC.eq_of_veblen_eq hz with h | h
    · exact ihx h (by rw [h, ← hz]; exact hqz)
    · exact ihy h (by rw [h, ← hz]; exact hqz)
  | @om x _ ihx =>
    intro hz hqz
    rcases (le_Om x).lt_or_eq with hlt | heq
    · exfalso
      rcases hπ with ⟨m, rfl⟩ | ⟨t, rfl⟩
      · have hx : x = S.psi d (S.I m) := Om_inj.1 (hz.trans (Om_psiI d m).symm)
        rw [hz, hx] at hlt; exact lt_irrefl _ hlt
      · exact not_Om_of_between (psiS_bounds d t).1 (psiS_bounds d t).2 x hz.symm
    · rw [← heq] at hz hqz; exact ihx hz hqz
  | @coll π' e hπ' _ hπK heK hown _ _ =>
    intro hz _
    have hππ : π' = π := sub_eq_of_psi_eq hπ' hπ hz
    subst hππ
    have hc := compare_psi hπ' hown hd
    rw [hz, compare_eq_iff_eq.2 rfl] at hc
    rw [← compare_eq_iff_eq.1 hc.symm]; exact ⟨heK, hπK⟩

/-- **The K-version of `InaccSeq.arg_mem_of_psi_mem`**: the own argument `d` of a collapse `ψ_π(d) ∈ K_q` with
`q ≤ ψ_π(d)` (and `q ≤ Λ`) is in `K_q`. -/
theorem uoArg (hqL : q ≤ S.Lam) {π d : Ordinal.{0}} (hπ : S.InR π) (hd : d ∈ S.CSet d (S.psi d π))
    (hK : UlK S s q (S.psi d π)) (hq : q ≤ S.psi d π) : UlK S s q d :=
  (uoArgU hπ hd _ (uoK_of_K hqL hK) rfl hq).1.toK

/-- **The subscript of a collapse `ψ_π(d) ∈ K_q`** (`d` own, `q ≤ ψ_π(d)`, `q ≤ Λ`) is in `K_q`. -/
theorem uoSub (hqL : q ≤ S.Lam) {π d : Ordinal.{0}} (hπ : S.InR π) (hd : d ∈ S.CSet d (S.psi d π))
    (hK : UlK S s q (S.psi d π)) (hq : q ≤ S.psi d π) : UlK S s q π :=
  (uoArgU hπ hd _ (uoK_of_K hqL hK) rfl hq).2.toK

end Googology.Trans.PoR.InaccPsi.R2.Uo
