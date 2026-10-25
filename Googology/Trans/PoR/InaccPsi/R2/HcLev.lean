import Googology.Trans.PoR.InaccPsi.R2.HbWFr

/-!
# HcLev: THE LEVEL FACTS AT EVERY VEBLEN LEVEL `β`, AND AT THE LIMIT LEVEL `ω`

`Hb.HbLev` states the closed form of the points of Veblen level `k + 1` (`k : ℕ`) through `Hb.hbN k`, the next fixed
point of `φ(k, ·)`.  The atoms `ϑˣ(Ω₁·β + t)` are defined at every level `β ∈ Tˣ ∩ Ω₁` (`Gl.glA`), and the closed
form needs no next fixed point: the point after `φ(β, i)` is `φ(β, i + 1)`.  Here:

* `hc_glA_succV` (**`ϑˣ(Ω₁·β + t) = φ(β, i)` ⇒ `ϑˣ(Ω₁·β + t + 1) = φ(β, i + 1)`, every level `β`**), `hc_glAV`
  (**the closed form `ϑˣ(Ω₁·β + P + ν) = φ(β, i + ν)` at every level `β`**);
* the limit level `ω`: `hcS Q = sup_k N_k(Q)` (**the least common fixed point of every `φ(k, ·)`, `k < ω`, above
  `Q`**), `hcS_veb`, `hcS_LuP`, `hcS_le`, `hcS_veb_eq` (`hcS(φ(ω, a)) = φ(ω, a+1)`), `hc_lt_S` (`u < hcS Q` ⇒
  `u < N_k(Q)` for some `k`); `hcNw Q` (**the least fixed point of `φ(ω, ·)` above `Q`**), `hcS_lt_Nw`, `hc_nofixW`
  (no fixed point of `φ(ω, ·)` in `[i, N_ω(P))`);
* at an `ε`-number base `x`: `hc_G_fix` (`φ(β, Γ_{x+1}) = Γ_{x+1}` for `β < Γ_{x+1}`), `hc_glA_baseW`,
  `hc_glA_fixW` (**`ϑˣ(Ω₁·ω + P) = hcS P = φ(ω, P+1)`** at a fixed point `P` of `φ(ω, ·)`), `hc_glA_GW`
  (**`ϑˣ(Ω₁·ω + Γ_{x+1}) = B_ω(x)`**), `hc_zetaW` (**`ζ = logend(d)`** for the point `ϑˣ(Ω₁·ω + P + d)` at a limit
  `d`), `hc_zeta_leW`.

No new axiom.  New definitions: `hcS`, `hcNw`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hc

open Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The closed form at every level `β` -/

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **The next point at every level `β`**: `ϑˣ(Ω₁·β + t) = φ(β, i)` ⇒ `ϑˣ(Ω₁·β + t + 1) = φ(β, i + 1)`. -/
theorem hc_glA_succV {β t i : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβq : β < gq 1 x) (ht : t + 1 < gq 1 x)
    (hi : glA β t x = veblen β i) : glA β (t + 1) x = veblen β (i + 1) := by
  obtain ⟨hβT, hβΩ⟩ := gm1_T hx hx1 hβq
  have ht' : t < gq 1 x := (lt_add_one t).trans ht
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 ht'
  obtain ⟨hsT, hs1⟩ := gm1_T hx hx1 ht
  obtain ⟨-, hxa, -, -, hβa, hta⟩ := glA_facts hx hx1 hβ1 hβT hβΩ htT ht1
  rw [hi] at hxa hβa hta
  have hlt : veblen β i < veblen β (i + 1) := (isNormal_veblen β).strictMono (lt_add_one i)
  refine le_antisymm ?_ ?_
  · refine glA_min hx hx1 hβ1 hβT hβΩ hsT hs1 ⟨_, rfl⟩ (hxa.trans hlt)
      ((Order.add_one_le_of_lt hta).trans_lt hlt) (hβa.trans hlt) (fun σ hσ => ?_)
    have hσt : σ ≤ t := Order.lt_add_one_iff.1 hσ
    obtain ⟨hσT, hσ1⟩ := gm1_T hx hx1 (lt_of_le_of_lt hσt ht')
    refine lt_of_le_of_lt ?_ hlt
    rw [← hi]
    exact (glA_le_iff hx hx1 hβ1 hβT hβΩ hσT hσ1 htT ht1).2 hσt
  · obtain ⟨j, hj⟩ := glA_P hx hx1 hβ1 hβT hβΩ hsT hs1
    have h1 : glA β t x < glA β (t + 1) x := glA_lt_of hx hx1 hβ1 hβT hβΩ htT hsT hs1 (lt_add_one t)
    rw [hi, ← hj] at h1
    rw [← hj]
    exact (isNormal_veblen β).monotone (Order.add_one_le_of_lt ((isNormal_veblen β).strictMono.lt_iff_lt.1 h1))

/-- **THE CLOSED FORM AT EVERY LEVEL `β`**: `ϑˣ(Ω₁·β + P + ν) = φ(β, i + ν)` (`ϑˣ(Ω₁·β + P) = φ(β, i)`) for every `ν`
with `P + ν < Γ_{x+2}` and no fixed point `i + ν'`, `ν' ≤ ν` a limit, of `φ(β, ·)`. -/
theorem hc_glAV {β P i : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβq : β < gq 1 x) (hPq : P < gq 1 x)
    (hG0 : glA β P x = veblen β i) : ∀ ν, P + ν < gq 1 x →
    (∀ ν', ν' ≤ ν → IsSuccLimit ν' → i + ν' < veblen β (i + ν')) →
    glA β (P + ν) x = veblen β (i + ν) := by
  obtain ⟨hβT, hβΩ⟩ := gm1_T hx hx1 hβq
  have hβ0 : β ≠ 0 := (lt_of_lt_of_le zero_lt_one hβ1).ne'
  obtain ⟨hGT, hG1⟩ := gm1_T hx hx1 hPq
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hq hfix
  obtain ⟨htT, ht1⟩ := gm1_T hx hx1 hq
  rcases Ordinal.zero_or_succ_or_isSuccLimit ν with h0 | ⟨d, hd⟩ | hlim
  · subst h0; rw [add_zero, add_zero]; exact hG0
  · have hd' : ν = d + 1 := by rw [← succ_eq_add_one]; first | exact hd | exact hd.symm
    subst hd'
    have hdq : P + d < gq 1 x := lt_of_le_of_lt (add_le_add le_rfl le_self_add) hq
    have IHd := IH d (lt_add_one d) hdq (fun ν' h hl => hfix ν' (h.trans le_self_add) hl)
    rw [← add_assoc] at hq ⊢
    rw [hc_glA_succV hx hx1 hβ1 hβq hq IHd, ← add_assoc]
  · have hval : ∀ ν'', ν'' < ν → glA β (P + ν'') x = veblen β (i + ν'') := fun ν'' h =>
      IH ν'' h ((add_lt_add_iff_left _).2 h |>.trans hq) (fun ν' h' hl => hfix ν' (h'.trans h.le) hl)
    set u := veblen β (i + ν) with hu
    have huE : InE u := gg_veblen_eps hβ0
    have hiu : veblen β i < u := (isNormal_veblen _).strictMono (lt_add_of_pos_right _ hlim.bot_lt)
    obtain ⟨-, hxa, -, -, h2a, hGa⟩ := glA_facts hx hx1 hβ1 hβT hβΩ hGT hG1
    rw [hG0] at hxa h2a hGa
    have htu : P + ν < u := (inE_indec huE).add_lt (hGa.trans hiu)
      ((le_add_self : ν ≤ i + ν).trans_lt (hfix ν le_rfl hlim))
    refine le_antisymm ?_ ?_
    · refine glA_min hx hx1 hβ1 hβT hβΩ htT ht1 ⟨_, rfl⟩ (hxa.trans hiu) htu (h2a.trans hiu) (fun σ hσ => ?_)
      rcases lt_or_ge σ P with hσP | hσP
      · obtain ⟨hσT, hσ1⟩ := gm1_T hx hx1 (hσP.trans hPq)
        have := glA_lt_of hx hx1 hβ1 hβT hβΩ hσT hGT hG1 hσP
        rw [hG0] at this
        exact this.trans hiu
      · obtain ⟨ν'', rfl⟩ := exists_add_of_le hσP
        have hν'' : ν'' < ν := (add_lt_add_iff_left _).1 hσ
        rw [hval ν'' hν'']
        exact (isNormal_veblen _).strictMono ((add_lt_add_iff_left _).2 hν'')
    · refine ((isNormal_veblen _).le_iff_forall_le (isSuccLimit_add _ hlim)).2 fun c hc => ?_
      rcases lt_or_ge c i with hci | hci
      · refine ((isNormal_veblen _).strictMono hci).le.trans ?_
        rw [← hG0]
        exact (glA_le_iff hx hx1 hβ1 hβT hβΩ hGT hG1 htT ht1).2 le_self_add
      · obtain ⟨c', rfl⟩ := exists_add_of_le hci
        have hc' : c' < ν := (add_lt_add_iff_left _).1 hc
        have hq' : P + c' < gq 1 x := ((add_lt_add_iff_left _).2 hc').trans hq
        obtain ⟨hcT, -⟩ := gm1_T hx hx1 hq'
        rw [← hval c' hc']
        exact (glA_lt_of hx hx1 hβ1 hβT hβΩ hcT htT ht1 ((add_lt_add_iff_left _).2 hc')).le

end Base

/-! ## The limit level `ω`: `hcS` and `hcNw` -/

/-- **`sup_k N_k(Q)`**: the least common fixed point of every `φ(k, ·)`, `k < ω`, above `Q`. -/
noncomputable def hcS (Q : Ordinal.{0}) : Ordinal.{0} := ⨆ k : ℕ, hbN k Q

theorem hcS_bdd (Q : Ordinal.{0}) : BddAbove (Set.range fun k : ℕ => hbN k Q) := Ordinal.bddAbove_range _

theorem hbN_le_S (k : ℕ) (Q : Ordinal.{0}) : hbN k Q ≤ hcS Q := le_ciSup (hcS_bdd Q) k

theorem hbN_lt_S (k : ℕ) (Q : Ordinal.{0}) : hbN k Q < hcS Q := (hbN_lt_succ k Q).trans_le (hbN_le_S (k + 1) Q)

theorem hcS_gt (Q : Ordinal.{0}) : Q < hcS Q := (hbN_gt 0 Q).trans (hbN_lt_S 0 Q)

theorem hcS_Bw (x : Ordinal.{0}) : hcS (lgG x) = hbBw x := rfl

/-- **`hcS Q` is a fixed point of every `φ(k, ·)`, `k < ω`.** -/
theorem hcS_veb (k : ℕ) (Q : Ordinal.{0}) : veblen (k : Ordinal.{0}) (hcS Q) = hcS Q := by
  unfold hcS
  rw [(isNormal_veblen (k : Ordinal.{0})).map_iSup (hcS_bdd Q)]
  refine le_antisymm (Ordinal.iSup_le fun n => ?_) (Ordinal.iSup_le fun n => ?_)
  · have h1 : veblen (k : Ordinal.{0}) (hbN n Q) ≤ veblen (k : Ordinal.{0}) (hbN (n + k) Q) :=
      (isNormal_veblen _).monotone (hbN_mono (Nat.le_add_right n k) _)
    rw [hb_fix_down (Nat.le_add_left k n) (hbN_fix (n + k) Q)] at h1
    exact h1.trans (Ordinal.le_iSup (fun n => hbN n Q) (n + k))
  · exact (right_le_veblen _ _).trans (Ordinal.le_iSup (fun n => veblen (k : Ordinal.{0}) (hbN n Q)) n)

theorem hc_LuPw_iff {u : Ordinal.{0}} : LuP ω u ↔ ∀ k : ℕ, veblen (k : Ordinal.{0}) u = u := by
  unfold LuP
  rw [mem_range_veblen omega0_ne_zero]
  refine ⟨fun h k => h _ (natCast_lt_omega0 k), fun h b hb => ?_⟩
  obtain ⟨n, rfl⟩ := lt_omega0.1 hb
  exact h n

theorem hcS_LuP (Q : Ordinal.{0}) : LuP ω (hcS Q) := hc_LuPw_iff.2 fun k => hcS_veb k Q

theorem hcS_E (Q : Ordinal.{0}) : InE (hcS Q) := by
  have h := hcS_veb 0 Q; rw [Nat.cast_zero, veblen_zero_apply] at h; exact h

/-- **Minimality**: a common fixed point of every `φ(k, ·)` above `Q` is `≥ hcS Q`. -/
theorem hcS_le {Q u : Ordinal.{0}} (hu : ∀ k : ℕ, veblen (k : Ordinal.{0}) u = u) (hQu : Q < u) : hcS Q ≤ u :=
  Ordinal.iSup_le fun k => hbN_le k (hu k) hQu

theorem hc_lt_S {Q u : Ordinal.{0}} (hu : u < hcS Q) : ∃ k : ℕ, u < hbN k Q := (lt_ciSup_iff (hcS_bdd Q)).1 hu

/-- **`hcS(φ(ω, a)) = φ(ω, a+1)`.** -/
theorem hcS_veb_eq (a : Ordinal.{0}) : hcS (veblen ω a) = veblen ω (a + 1) := by
  have hlt : veblen ω a < veblen ω (a + 1) := (isNormal_veblen ω).strictMono (lt_add_one a)
  refine le_antisymm (hcS_le (hc_LuPw_iff.1 ⟨_, rfl⟩) hlt) ?_
  obtain ⟨b, hb⟩ := hcS_LuP (veblen ω a)
  have hab : veblen ω a < veblen ω b := by rw [hb]; exact hcS_gt _
  rw [← hb]
  exact (isNormal_veblen _).monotone (Order.add_one_le_of_lt ((isNormal_veblen _).strictMono.lt_iff_lt.1 hab))

/-- A fixed point of `φ(ω, ·)` is a fixed point of every `φ(k, ·)`. -/
theorem hc_fixW_k {P : Ordinal.{0}} (hP : veblen ω P = P) (k : ℕ) : veblen (k : Ordinal.{0}) P = P := by
  have := veblen_veblen_of_lt (natCast_lt_omega0 k) P; rwa [hP] at this

theorem hc_fixW_E {P : Ordinal.{0}} (hP : veblen ω P = P) : InE P := by
  have h := hc_fixW_k hP 0; rw [Nat.cast_zero, veblen_zero_apply] at h; exact h

theorem hc_LuPw1 {P : Ordinal.{0}} (hP : veblen ω P = P) : LuP (ω + 1) P := by
  unfold LuP
  rw [mem_range_veblen (by simp)]
  intro b hb
  rcases lt_or_ge b ω with hbω | hbω
  · have := veblen_veblen_of_lt hbω P; rwa [hP] at this
  · rw [le_antisymm (Order.lt_add_one_iff.1 hb) hbω]; exact hP

/-- `hcS P = φ(ω, P + 1)` at a fixed point `P` of `φ(ω, ·)`. -/
theorem hcS_fix {P : Ordinal.{0}} (hP : veblen ω P = P) : hcS P = veblen ω (P + 1) := by
  conv_lhs => rw [← hP]
  exact hcS_veb_eq P

/-- **The least fixed point of `φ(ω, ·)` above `Q`.** -/
noncomputable def hcNw (Q : Ordinal.{0}) : Ordinal.{0} := nfp (veblen ω) (Q + 1)

theorem hcNw_fix (Q : Ordinal.{0}) : veblen ω (hcNw Q) = hcNw Q := nfp_fp (isNormal_veblen _) _

theorem hcNw_gt (Q : Ordinal.{0}) : Q < hcNw Q := (lt_add_one Q).trans_le (le_nfp _ _)

theorem hcNw_le {Q j : Ordinal.{0}} (hj : veblen ω j = j) (hQj : Q < j) : hcNw Q ≤ j :=
  nfp_le_fp (isNormal_veblen _).strictMono.monotone (Order.add_one_le_of_lt hQj) hj.le

theorem hcNw_E (Q : Ordinal.{0}) : InE (hcNw Q) := hc_fixW_E (hcNw_fix Q)

theorem hcNw_lim (Q : Ordinal.{0}) : IsSuccLimit (hcNw Q) := ev_isSuccLimit_of_inE (hcNw_E Q)

/-- **`hcS P < N_ω(P)`** at a fixed point `P` of `φ(ω, ·)`. -/
theorem hcS_lt_Nw {P : Ordinal.{0}} (hP : veblen ω P = P) : hcS P < hcNw P := by
  rw [hcS_fix hP]
  have h := (isNormal_veblen ω).strictMono ((hcNw_lim P).add_one_lt (hcNw_gt P))
  rwa [hcNw_fix] at h

/-- `N_k(Q) < N_ω(Q)`. -/
theorem hbN_lt_Nw (k : ℕ) (Q : Ordinal.{0}) : hbN k Q < hcNw Q :=
  (hbN_lt_S k Q).trans_le (hcS_le (hc_fixW_k (hcNw_fix Q)) (hcNw_gt Q))

/-- **No fixed point of `φ(ω, ·)` in `[i, N_ω(P))`** when `P < φ(ω, i)`. -/
theorem hc_nofixW {P i j : Ordinal.{0}} (hi : P < veblen ω i) (hij : i ≤ j) (hjB : veblen ω j < hcNw P) :
    j < veblen ω j := by
  rcases (right_le_veblen ω j).lt_or_eq with h | h
  · exact h
  · exfalso
    have hPj : P < j := by
      have h1 : veblen ω i ≤ veblen ω j := (isNormal_veblen _).monotone hij
      rw [← h] at h1
      exact hi.trans_le h1
    exact absurd hjB (not_lt.2 ((hcNw_le h.symm hPj).trans h.le))

/-! ## The points of level `ω` at an `ε`-number base -/

section BaseW

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem hc_om_T : ω ∈ Tset x ∧ ω < Om1 := gm1_T hx hx1 (omega0_lt_inE (gm1_facts hx hx1).2.2.2)

theorem hc_om_q : ω < gq 1 x := omega0_lt_inE (gm1_facts hx hx1).2.2.2

omit hx hx1 in
theorem hc_one_le_om : (1 : Ordinal.{0}) ≤ ω := one_lt_omega0.le

/-- **`φ(β, Γ_{x+1}) = Γ_{x+1}`** for every `1 ≤ β < Γ_{x+1}`. -/
theorem hc_G_fix {β : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβ : β < lgG x) : veblen β (lgG x) = lgG x := by
  obtain ⟨hβT, hβΩ⟩ := gl_T_of_lt_G hx hx1 hβ
  obtain ⟨-, -, -, hGE, -⟩ := lgG_facts hx hx1
  refine le_antisymm (((isNormal_veblen β).le_iff_forall_le (ev_isSuccLimit_of_inE hGE)).2 fun j hj => ?_)
    (right_le_veblen _ _)
  obtain ⟨hjT, hj1⟩ := gl_T_of_lt_G hx hx1 hj
  exact ((glA_veb_le hx hx1 hβ1 hβT hβΩ hjT hj1).trans_lt (glA_lt_G hx hx1 hβ hj)).le

theorem hc_G_fixW : veblen ω (lgG x) = lgG x :=
  hc_G_fix hx hx1 hc_one_le_om (omega0_lt_inE (lgG_facts hx hx1).2.2.2.1)

/-- **`ϑˣ(Ω₁·ω + P) = hcS P`** when every `ϑˣ(Ω₁·ω + σ)`, `σ < P`, lies below `P`. -/
theorem hc_glA_baseW {P : Ordinal.{0}} (hlow : ∀ σ, σ < P → glA ω σ x < P) (hxP : x < P) (hPq : P < gq 1 x) :
    glA ω P x = hcS P := by
  obtain ⟨hPT, hP1⟩ := gm1_T hx hx1 hPq
  obtain ⟨hωT, hω1⟩ := hc_om_T hx hx1
  have hPS : P < hcS P := hcS_gt P
  refine le_antisymm ?_ ?_
  · exact glA_min hx hx1 hc_one_le_om hωT hω1 hPT hP1 (hcS_LuP P) (hxP.trans hPS) hPS
      (omega0_lt_inE (hcS_E P)) (fun σ hσ => (hlow σ hσ).trans hPS)
  · obtain ⟨-, -, -, -, -, hta⟩ := glA_facts hx hx1 hc_one_le_om hωT hω1 hPT hP1
    exact hcS_le (hc_LuPw_iff.1 (glA_P hx hx1 hc_one_le_om hωT hω1 hPT hP1)) hta

/-- `ϑˣ(Ω₁·ω + σ) < P` for every `σ < P`, `P ∈ (x, Γ_{x+2})` a fixed point of `φ(ω, ·)`. -/
theorem hc_lowW {P : Ordinal.{0}} (hP : veblen ω P = P) (hxP : x < P) (hPq : P < gq 1 x) :
    ∀ σ, σ < P → glA ω σ x < P := by
  obtain ⟨hωT, hω1⟩ := hc_om_T hx hx1
  have hPE : InE P := hc_fixW_E hP
  have hP2 : LuP ω P := ⟨P, hP⟩
  have hP3 : LuP (ω + 1) P := hc_LuPw1 hP
  have hωP : ω < P := omega0_lt_inE hPE
  intro σ
  induction σ using WellFoundedLT.induction with
  | ind σ IH =>
  intro hσ
  obtain ⟨hσT, hσ1⟩ := gm1_T hx hx1 (hσ.trans hPq)
  have hle : glA ω σ x ≤ P := glA_min hx hx1 hc_one_le_om hωT hω1 hσT hσ1 hP2 hxP hσ hωP
    (fun σ' h' => IH σ' h' (h'.trans hσ))
  exact lt_of_le_of_ne hle (fun e => glA_notP hx hx1 hc_one_le_om hωT hω1 hσT hσ1 (by rw [e]; exact hP3))

/-- **`ϑˣ(Ω₁·ω + P) = hcS P = φ(ω, P + 1)`** at a fixed point `P ∈ (x, Γ_{x+2})` of `φ(ω, ·)`. -/
theorem hc_glA_fixW {P : Ordinal.{0}} (hP : veblen ω P = P) (hxP : x < P) (hPq : P < gq 1 x) :
    glA ω P x = hcS P := hc_glA_baseW hx hx1 (hc_lowW hx hx1 hP hxP hPq) hxP hPq

/-- **`ϑˣ(Ω₁·ω + Γ_{x+1}) = B_ω(x) = φ(ω, Γ_{x+1} + 1)`.** -/
theorem hc_glA_GW : glA ω (lgG x) x = hbBw x ∧ hbBw x = veblen ω (lgG x + 1) := by
  obtain ⟨-, hxG, -, -, -⟩ := lgG_facts hx hx1
  have hG := hc_G_fixW hx hx1
  refine ⟨hc_glA_fixW hx hx1 hG hxG (mg_lgG_lt_G1 hx hx1), ?_⟩
  rw [← hcS_Bw]; exact hcS_fix hG

/-- **`ζ = logend(d)`** for the point `ϑˣ(Ω₁·ω + P + d) = φ(ω, i + d)` at a limit `d`. -/
theorem hc_zetaW {P i d : Ordinal.{0}} (hPq : P < gq 1 x) (hG0 : glA ω P x = veblen ω i)
    (hdq : P + d < gq 1 x) (hfix : ∀ ν', ν' ≤ d → IsSuccLimit ν' → i + ν' < veblen ω (i + ν'))
    (hlim : IsSuccLimit d) : luZeta x ω (P + d) = lg d := by
  classical
  have hd0 : d ≠ 0 := hlim.bot_lt.ne'
  obtain ⟨hωT, hω1⟩ := hc_om_T hx hx1
  have hωq := hc_om_q hx hx1
  have hval := hc_glAV hx hx1 hc_one_le_om hωq hPq hG0 d hdq hfix
  obtain ⟨hdT, hd1⟩ := gm1_T hx hx1 hdq
  obtain ⟨-, -, -, -, -, htE⟩ := glA_facts hx hx1 hc_one_le_om hωT hω1 hdT hd1
  rw [hval] at htE
  obtain ⟨a, ha, hta⟩ := ((isNormal_veblen _).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 htE
  have hc'' : a - i < d := by
    rcases lt_or_ge a i with hai | hai
    · rw [Ordinal.sub_eq_zero_iff_le.2 hai.le]; exact hlim.bot_lt
    · have : i + (a - i) < i + d := by rw [Ordinal.add_sub_cancel_of_le hai]; exact ha
      exact (add_lt_add_iff_left _).1 this
  have hq' : P + (a - i) < gq 1 x := ((add_lt_add_iff_left _).2 hc'').trans hdq
  have hv' : glA ω (P + (a - i)) x = veblen ω (i + (a - i)) :=
    hc_glAV hx hx1 hc_one_le_om hωq hPq hG0 (a - i) hq' (fun ν' h' hl => hfix ν' (h'.trans hc''.le) hl)
  have hcond : P + d < vt x (Om1 * ω + (P + (a - i))) := by
    have e : vt x (Om1 * ω + (P + (a - i))) = glA ω (P + (a - i)) x := rfl
    rw [e, hv']
    exact hta.trans_le ((isNormal_veblen _).monotone (Ordinal.le_add_sub a i))
  unfold luZeta
  rw [if_pos ⟨P + (a - i), (add_lt_add_iff_left _).2 hc'', hcond⟩, gz_lg_add _ hd0]

omit hx hx1 in
/-- `ζ ≤ logend(d)` for the point `ϑˣ(Ω₁·ω + P + d)`, `d ≠ 0`. -/
theorem hc_zeta_leW {P d : Ordinal.{0}} (hd0 : d ≠ 0) : luZeta x ω (P + d) ≤ lg d :=
  lu_zeta_le_lg.trans (gz_lg_add P hd0).le

end BaseW

end Googology.Trans.PoR.InaccPsi.R2.Hc
