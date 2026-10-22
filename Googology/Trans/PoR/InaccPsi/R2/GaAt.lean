import Googology.Trans.PoR.InaccPsi.R2.LpTow
import Googology.Trans.PoR.InaccPsi.R2.LdHull

/-!
# The atoms `Γ_{Ω₁+1+k} = ψ_{Ω₂}(k)` (`k < ω`) and their limit `Γ_{Ω₁+ω} = ψ_{Ω₂}(ω)`

`R2.LgCl` has one atom `Γ_{Ω₁+1} = ψ_{Ω₂}(0)` and stops below `Γ' = Γ_{Ω₁+2}`.  Here the strongly critical ordinals
between `Ω₁` and `Γ_{Ω₁+ω}`:

* `gaG k` (**`gaG 0 = Γ_{Ω₁+1}`, `gaG (k+1)` the least strongly critical ordinal above `gaG k`**), `gaW` (**the least
  strongly critical ordinal above every `gaG k`**), `gaAt = {gaG k | k < ω}`;
* `gaPsi_le` (**`ψ_{Ω₂}(a) ≤ b`** for a strongly critical `b > Ω₁` with `ψ_{Ω₂}(e) < b` for every `e < a`: every
  member of `Cl(a, b)` below `Ω₂` is below `b`);
* `gaG_spec` (**`ψ_{Ω₂}(k) = gaG k`**, strongly critical, above `Ω₁`), `gaW_psi` (**`ψ_{Ω₂}(ω) = gaW`**), `gaW_spec`,
  `gaW_lt_Om2`, `gaW_sup` (`gaW = sup_k gaG k`), `gaG_one` (`gaG 1 = Γ'`);
* `gaSC_cases` (**every strongly critical `s` with `Ω₁ < s < gaW` is some `gaG k`**), `gaAt_GxAt`, `gaG_mem`
  (`gaG k ∈ Cl(a, b)` for `k < a`), `gaW_mem`.

No new axiom.  New definitions: `gaG`, `gaW`, `gaAt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ga

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx

/-- **The strongly critical ordinals above `Ω₁`**: `gaG 0 = Γ_{Ω₁+1}`, `gaG (k+1)` the least one above `gaG k`. -/
noncomputable def gaG : ℕ → Ordinal.{0}
  | 0 => ggGam
  | k + 1 => sInf {b | SC b ∧ gaG k < b}

/-- **`Γ_{Ω₁+ω}`**: the least strongly critical ordinal above every `gaG k`. -/
noncomputable def gaW : Ordinal.{0} := sInf {b | SC b ∧ ∀ k : ℕ, gaG k < b}

/-- The atoms `gaG k`, `k < ω`. -/
def gaAt : Set Ordinal.{0} := {s | ∃ k : ℕ, s = gaG k}

theorem gaG_zero : gaG 0 = ggGam := rfl

theorem gaG_one : gaG 1 = lgGam' := rfl

variable {S : InaccSeq.{0}}

theorem ga_nat_mem (a b : Ordinal.{0}) : ∀ n : ℕ, (n : Ordinal.{0}) ∈ S.CSet a b
  | 0 => by rw [Nat.cast_zero]; exact CSet.zero_mem _ _
  | n + 1 => by rw [Nat.cast_succ]; exact CSet.succ_mem (ga_nat_mem a b n)

theorem ga_Om2_mem (a b : Ordinal.{0}) : Om (1 + 1 : Ordinal.{0}) ∈ S.CSet a b :=
  CSet.Om_mem (CSet.add_mem (CSet.one_mem _ _) (CSet.one_mem _ _))

/-- **`ψ_{Ω₂}(a) ≤ b`** for a strongly critical `b > Ω₁` with `ψ_{Ω₂}(e) < b` for every `e < a`. -/
theorem gaPsi_le (S : InaccSeq.{0}) {a b : Ordinal.{0}} (hb : SC b) (hOb : Om 1 < b)
    (he : ∀ e < a, S.psi e (Om (1 + 1)) < b) : S.psi a (Om (1 + 1)) ≤ b := by
  refine psi_le_of_good (ga_Om2_mem _ _) ?_
  intro x hx
  induction hx with
  | small h => exact fun _ => h
  | zero => exact fun _ => hb.1
  | inacc n =>
    intro h
    exact absurd (h.trans (mxOm2_lt_I n)) (lt_irrefl _)
  | inaccW =>
    intro h
    exact absurd (h.trans mxOm2_lt_Iw) (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    intro h
    exact hb.isPrincipal (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    intro h
    exact hb.2 _ (ihx (lt_of_le_of_lt (left_le_veblen x y) h)) _ (ihy (lt_of_le_of_lt (right_le_veblen x y) h))
  | @om x _ _ =>
    intro h
    have h2 : x < 1 + 1 := Om_lt_Om.1 h
    rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
    · rw [Order.lt_one_iff] at h0; rw [h0, Om_zero]; exact hb.1
    · rw [h1]; exact hOb
  | @coll π e hπ _ _ _ _ =>
    intro h
    rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
    · exfalso
      have h2 : Om (1 + 1 : Ordinal.{0}) < S.psi e.1 (S.I n) :=
        lt_psi_of_mem (InR_I n) (mxOm2_mem _ _) (mxOm2_lt_I n)
      exact absurd (h2.trans h) (lt_irrefl _)
    rcases eq_or_ne s 0 with rfl | hs0
    · have := psi_lt (InR_Om_succ (S := S) 0) e.1
      rw [zero_add] at this ⊢
      exact this.trans hOb
    rcases eq_or_ne s 1 with rfl | hs1
    · exact he e.1 e.2
    · exfalso
      have h2s : 1 + 1 ≤ s := Order.add_one_le_of_lt (lt_of_le_of_ne
        (Order.one_le_iff_ne_zero.2 hs0) (Ne.symm hs1))
      have h2 := (Om_lt_psiS (S := S) e.1 s).2 h2s
      exact absurd (h2.trans h) (lt_irrefl _)

theorem ga_psi_SC (a : Ordinal.{0}) : SC (S.psi a (Om (1 + 1))) := SC_psi (InR_Om_succ 1) a

theorem ga_Om1_lt_psi (a : Ordinal.{0}) : Om 1 < S.psi a (Om (1 + 1)) := (psiS_bounds a 1).1

theorem ga_psi_lt_nat {m n : ℕ} (h : m < n) :
    S.psi (m : Ordinal.{0}) (Om (1 + 1)) < S.psi (n : Ordinal.{0}) (Om (1 + 1)) :=
  psi_lt_psi_of_mem (InR_Om_succ 1) (by exact_mod_cast h) (ga_nat_mem _ _ m)

/-- **`ψ_{Ω₂}(k) = gaG k`**, strongly critical and above `Ω₁`. -/
theorem gaG_spec (S : InaccSeq.{0}) :
    ∀ k : ℕ, S.psi (k : Ordinal.{0}) (Om (1 + 1)) = gaG k ∧ SC (gaG k) ∧ Om 1 < gaG k
  | 0 => by
    rw [Nat.cast_zero, lg_Gam_psi S]; exact ⟨rfl, ggGam_spec.1, ggGam_spec.2⟩
  | k + 1 => by
    obtain ⟨ih, ihS, ihO⟩ := gaG_spec S k
    have hin : S.psi ((k + 1 : ℕ) : Ordinal.{0}) (Om (1 + 1)) ∈ {b | SC b ∧ gaG k < b} :=
      ⟨ga_psi_SC _, ih ▸ ga_psi_lt_nat (Nat.lt_succ_self k)⟩
    have hne : {b | SC b ∧ gaG k < b}.Nonempty := ⟨_, hin⟩
    have hmem : gaG (k + 1) ∈ {b | SC b ∧ gaG k < b} := csInf_mem hne
    have hle : gaG (k + 1) ≤ S.psi ((k + 1 : ℕ) : Ordinal.{0}) (Om (1 + 1)) := csInf_le' hin
    have hge : S.psi ((k + 1 : ℕ) : Ordinal.{0}) (Om (1 + 1)) ≤ gaG (k + 1) := by
      refine gaPsi_le S hmem.1 (ihO.trans hmem.2) fun e he => ?_
      have hek : e ≤ k := by
        rw [Nat.cast_succ] at he; exact Order.lt_add_one_iff.1 he
      exact ((psi_mono (InR_Om_succ 1) hek).1.trans_eq ih).trans_lt hmem.2
    exact ⟨le_antisymm hge hle, hmem.1, ihO.trans hmem.2⟩

theorem gaG_SC (S : InaccSeq.{0}) (k : ℕ) : SC (gaG k) := (gaG_spec S k).2.1

theorem gaG_Om1_lt (S : InaccSeq.{0}) (k : ℕ) : Om 1 < gaG k := (gaG_spec S k).2.2

theorem gaG_lt_succ (S : InaccSeq.{0}) (k : ℕ) : gaG k < gaG (k + 1) := by
  rw [← (gaG_spec S k).1, ← (gaG_spec S (k + 1)).1]; exact ga_psi_lt_nat (Nat.lt_succ_self k)

theorem gaG_strictMono (S : InaccSeq.{0}) : StrictMono gaG := strictMono_nat_of_lt_succ (gaG_lt_succ S)

/-- `gaG (k+1)` is at most every strongly critical ordinal above `gaG k`. -/
theorem gaG_succ_le {k : ℕ} {b : Ordinal.{0}} (hb : SC b) (h : gaG k < b) : gaG (k + 1) ≤ b :=
  csInf_le' (s := {b | SC b ∧ gaG k < b}) ⟨hb, h⟩

theorem gaG_lt_Om2 (S : InaccSeq.{0}) (k : ℕ) : gaG k < Om (1 + 1) := by
  rw [← (gaG_spec S k).1]; exact psi_lt (InR_Om_succ 1) _

/-- **`ψ_{Ω₂}(ω) = gaW`**: strongly critical, above every `gaG k`, below `Ω₂`. -/
theorem gaW_psi (S : InaccSeq.{0}) : S.psi ω (Om (1 + 1)) = gaW ∧ SC gaW ∧ ∀ k : ℕ, gaG k < gaW := by
  have hlt : ∀ k : ℕ, gaG k < S.psi ω (Om (1 + 1)) := fun k => by
    rw [← (gaG_spec S k).1]
    exact psi_lt_psi_of_mem (InR_Om_succ 1) (natCast_lt_omega0 k) (ga_nat_mem _ _ k)
  have hin : S.psi ω (Om (1 + 1)) ∈ {b | SC b ∧ ∀ k : ℕ, gaG k < b} := ⟨ga_psi_SC _, hlt⟩
  have hne : {b | SC b ∧ ∀ k : ℕ, gaG k < b}.Nonempty := ⟨_, hin⟩
  have hmem : gaW ∈ {b | SC b ∧ ∀ k : ℕ, gaG k < b} := csInf_mem hne
  have hle : gaW ≤ S.psi ω (Om (1 + 1)) := csInf_le' hin
  have hge : S.psi ω (Om (1 + 1)) ≤ gaW := by
    refine gaPsi_le S hmem.1 ((gaG_Om1_lt S 0).trans (hmem.2 0)) fun e he => ?_
    obtain ⟨n, rfl⟩ := lt_omega0.1 he
    rw [(gaG_spec S n).1]; exact hmem.2 n
  exact ⟨le_antisymm hge hle, hmem.1, hmem.2⟩

theorem gaW_SC (S : InaccSeq.{0}) : SC gaW := (gaW_psi S).2.1

theorem gaG_lt_W (S : InaccSeq.{0}) (k : ℕ) : gaG k < gaW := (gaW_psi S).2.2 k

theorem gaW_le {b : Ordinal.{0}} (hb : SC b) (h : ∀ k : ℕ, gaG k < b) : gaW ≤ b :=
  csInf_le' (s := {b | SC b ∧ ∀ k : ℕ, gaG k < b}) ⟨hb, h⟩

theorem gaW_lt_Om2 (S : InaccSeq.{0}) : gaW < Om (1 + 1) := by
  rw [← (gaW_psi S).1]; exact psi_lt (InR_Om_succ 1) _

theorem ga_Om1_lt_W (S : InaccSeq.{0}) : Om 1 < gaW := (gaG_Om1_lt S 0).trans (gaG_lt_W S 0)

/-- **`gaW = sup_k gaG k`.** -/
theorem gaW_sup (S : InaccSeq.{0}) : gaW = ⨆ k : ℕ, gaG k := by
  have hbdd : BddAbove (range gaG) := Ordinal.bddAbove_of_small
  have hle1 : ∀ k : ℕ, gaG k < ⨆ k : ℕ, gaG k := fun k =>
    (gaG_lt_succ S k).trans_le (le_ciSup hbdd (k + 1))
  refine le_antisymm (gaW_le ⟨lt_of_le_of_lt zero_le (hle1 0), fun x hx y hy => ?_⟩ hle1)
    (ciSup_le' fun k => (gaG_lt_W S k).le)
  obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 hx
  obtain ⟨m, hm⟩ := (lt_ciSup_iff hbdd).1 hy
  have h1 : x < gaG (max n m) := hn.trans_le ((gaG_strictMono S).monotone (le_max_left n m))
  have h2 : y < gaG (max n m) := hm.trans_le ((gaG_strictMono S).monotone (le_max_right n m))
  exact ((gaG_SC S _).2 x h1 y h2).trans (hle1 _)

/-- **Every strongly critical `s` with `Ω₁ < s < gaW` is some `gaG k`.** -/
theorem gaSC_cases {s : Ordinal.{0}} (hs : SC s) (h1 : Om 1 < s) (h2 : s < gaW) :
    ∃ k : ℕ, s = gaG k := by
  by_contra hne
  push Not at hne
  have hall : ∀ k : ℕ, gaG k < s := by
    intro k
    induction k with
    | zero => exact lt_of_le_of_ne (ggGam_le hs h1) (hne 0).symm
    | succ k ih => exact lt_of_le_of_ne (gaG_succ_le hs ih) (hne (k + 1)).symm
  exact absurd (gaW_le hs hall) (not_le.2 h2)

/-- The atoms are strongly critical and above `Ω₁`. -/
theorem gaAt_GxAt (S : InaccSeq.{0}) : GxAt gaAt := by
  rintro s ⟨k, rfl⟩; exact ⟨gaG_SC S k, gaG_Om1_lt S k⟩

theorem gaAt_lt_W (S : InaccSeq.{0}) {s : Ordinal.{0}} (hs : s ∈ gaAt) : s < gaW := by
  obtain ⟨k, rfl⟩ := hs; exact gaG_lt_W S k

/-- `gaG k ∈ Cl(a, b)` for `k < a`. -/
theorem gaG_mem {a b : Ordinal.{0}} {k : ℕ} (hk : (k : Ordinal.{0}) < a) : gaG k ∈ S.CSet a b := by
  rw [← (gaG_spec S k).1]
  exact CSet.psi_mem hk (InR_Om_succ 1) (ga_Om2_mem _ _) (ga_nat_mem _ _ k)

theorem gaAt_mem {a b s : Ordinal.{0}} (ha : ω ≤ a) (hs : s ∈ gaAt) : s ∈ S.CSet a b := by
  obtain ⟨k, rfl⟩ := hs; exact gaG_mem ((natCast_lt_omega0 k).trans_le ha)

/-- `gaW ∈ Cl(a, b)` for `ω < a`. -/
theorem gaW_mem {a b : Ordinal.{0}} (ha : ω < a) : gaW ∈ S.CSet a b := by
  rw [← (gaW_psi S).1]
  have hω : ω ∈ S.CSet a b := by
    have := CSet.phi_mem (CSet.zero_mem (S := S) a b) (CSet.one_mem a b)
    rwa [veblen_zero_apply, opow_one] at this
  exact CSet.psi_mem ha (InR_Om_succ 1) (ga_Om2_mem _ _) hω

theorem gaG_le_of_le {j k : ℕ} (S : InaccSeq.{0}) (h : j ≤ k) : gaG j ≤ gaG k := (gaG_strictMono S).monotone h

end Googology.Trans.PoR.InaccPsi.R2.Ga
