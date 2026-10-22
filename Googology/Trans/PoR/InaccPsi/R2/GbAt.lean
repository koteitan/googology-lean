import Googology.Trans.PoR.InaccPsi.R2.GaTow

/-!
# The atoms `Γ_{Ω₁+ω+k}` and the codes with them, up to `Γ_{Ω₁+ω·2}`

`R2.GaAt` / `R2.GaCl` have the atoms `gaG k = ψ_{Ω₂}(k) = Γ_{Ω₁+1+k}` and the bound `gaW = ψ_{Ω₂}(ω) = Γ_{Ω₁+ω}`.  Here
the atoms are all `gaG k` and all `gbH k = ψ_{Ω₂}(ω + k) = Γ_{Ω₁+ω+k}` (`gbH 0 = gaW`), the bound `gbV = ψ_{Ω₂}(ω·2) =
Γ_{Ω₁+ω·2}`:

* `gbH_spec` (**`ψ_{Ω₂}(ω + k) = gbH k`**, strongly critical, above `Ω₁`), `gbV_psi`, `gbV_sup` (**`gbV = sup_k gbH
  k`**), `gbSC_cases` (**every strongly critical `s ∈ (Ω₁, gbV)` is an atom**), `gbAt_GxAt`, `gbAt_mem`, `gb_A_ge`
  (`ω·2 ≤ A_η`);
* the codes `GxCl Z gbAt`: `gbCl_lt_V`, `gbCl_mem_CSet`, `gbCl_of_CSet` (**the hull below `gbV` consists of codes**),
  `ga_of_gbCl` / `gb_of_gaCl` and `gbTh_eq_gaTh` (**below `Γ_{Ω₁+ω}` the codes and readings are those of `R2.GaCl`**);
* the readings: `gbTh_W` (**`Θ_y(Γ_{Ω₁+ω}) = sup_k Θ_y(Γ_{Ω₁+1+k})`**), `gbTh_H` (**the reading of every `gbH k` is
  strongly critical, in `(y, Ω₁)`**), `gbTh_lt_Om1`;
* `GbPoly X E` (terms for the codes below `E`), `gbPoly_of_SC`, `gbPoly_of_ga` (**`GaPoly X E` with `E ≤ Γ_{Ω₁+ω}`
  gives `GbPoly X E`**).

No new axiom.  New definitions: `gbH`, `gbV`, `gbAt`, `GbPoly`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Xt

/-- **The strongly critical ordinals from `Γ_{Ω₁+ω}` on**: `gbH 0 = gaW`, `gbH (k+1)` the least one above `gbH k`. -/
noncomputable def gbH : ℕ → Ordinal.{0}
  | 0 => gaW
  | k + 1 => sInf {b | SC b ∧ gbH k < b}

/-- **`Γ_{Ω₁+ω·2}`**: the least strongly critical ordinal above every `gbH k`. -/
noncomputable def gbV : Ordinal.{0} := sInf {b | SC b ∧ ∀ k : ℕ, gbH k < b}

/-- The atoms: every `gaG k` and every `gbH k`. -/
def gbAt : Set Ordinal.{0} := {s | (∃ k : ℕ, s = gaG k) ∨ ∃ k : ℕ, s = gbH k}

theorem gbH_zero : gbH 0 = gaW := rfl

theorem gaAt_sub_gbAt : gaAt ⊆ gbAt := fun _ hs => Or.inl hs

variable {S : InaccSeq.{0}}

theorem gb_omega_mem (a b : Ordinal.{0}) : (ω : Ordinal.{0}) ∈ S.CSet a b := by
  have := CSet.phi_mem (CSet.zero_mem (S := S) a b) (CSet.one_mem a b)
  rwa [veblen_zero_apply, opow_one] at this

theorem gb_off_mem (a b : Ordinal.{0}) (k : ℕ) : ω + (k : Ordinal.{0}) ∈ S.CSet a b :=
  CSet.add_mem (gb_omega_mem a b) (ga_nat_mem a b k)

theorem gb_psi_lt_off {m n : ℕ} (h : m < n) :
    S.psi (ω + (m : Ordinal.{0})) (Om (1 + 1)) < S.psi (ω + (n : Ordinal.{0})) (Om (1 + 1)) :=
  psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left _).2 (by exact_mod_cast h)) (gb_off_mem _ _ m)

/-- **`ψ_{Ω₂}(ω + k) = gbH k`**, strongly critical and above `Ω₁`. -/
theorem gbH_spec (S : InaccSeq.{0}) :
    ∀ k : ℕ, S.psi (ω + (k : Ordinal.{0})) (Om (1 + 1)) = gbH k ∧ SC (gbH k) ∧ Om 1 < gbH k
  | 0 => by
    rw [Nat.cast_zero, add_zero, (gaW_psi S).1]
    exact ⟨rfl, gaW_SC S, ga_Om1_lt_W S⟩
  | k + 1 => by
    obtain ⟨ih, -, ihO⟩ := gbH_spec S k
    have hin : S.psi (ω + ((k + 1 : ℕ) : Ordinal.{0})) (Om (1 + 1)) ∈ {b | SC b ∧ gbH k < b} :=
      ⟨ga_psi_SC _, ih ▸ gb_psi_lt_off (Nat.lt_succ_self k)⟩
    have hne : {b | SC b ∧ gbH k < b}.Nonempty := ⟨_, hin⟩
    have hmem : gbH (k + 1) ∈ {b | SC b ∧ gbH k < b} := csInf_mem hne
    have hle : gbH (k + 1) ≤ S.psi (ω + ((k + 1 : ℕ) : Ordinal.{0})) (Om (1 + 1)) := csInf_le' hin
    have hge : S.psi (ω + ((k + 1 : ℕ) : Ordinal.{0})) (Om (1 + 1)) ≤ gbH (k + 1) := by
      refine gaPsi_le S hmem.1 (ihO.trans hmem.2) fun e he => ?_
      have hek : e ≤ ω + (k : Ordinal.{0}) := by
        rw [Nat.cast_succ, ← add_assoc] at he; exact Order.lt_add_one_iff.1 he
      exact ((psi_mono (InR_Om_succ 1) hek).1.trans_eq ih).trans_lt hmem.2
    exact ⟨le_antisymm hge hle, hmem.1, ihO.trans hmem.2⟩

theorem gbH_SC (S : InaccSeq.{0}) (k : ℕ) : SC (gbH k) := (gbH_spec S k).2.1

theorem gbH_Om1_lt (S : InaccSeq.{0}) (k : ℕ) : Om 1 < gbH k := (gbH_spec S k).2.2

theorem gbH_lt_succ (S : InaccSeq.{0}) (k : ℕ) : gbH k < gbH (k + 1) := by
  rw [← (gbH_spec S k).1, ← (gbH_spec S (k + 1)).1]; exact gb_psi_lt_off (Nat.lt_succ_self k)

theorem gbH_strictMono (S : InaccSeq.{0}) : StrictMono gbH := strictMono_nat_of_lt_succ (gbH_lt_succ S)

/-- `gbH (k+1)` is at most every strongly critical ordinal above `gbH k`. -/
theorem gbH_succ_le {k : ℕ} {b : Ordinal.{0}} (hb : SC b) (h : gbH k < b) : gbH (k + 1) ≤ b :=
  csInf_le' (s := {b | SC b ∧ gbH k < b}) ⟨hb, h⟩

theorem gaW_le_gbH (S : InaccSeq.{0}) (k : ℕ) : gaW ≤ gbH k := (gbH_strictMono S).monotone (Nat.zero_le k)

theorem gaG_lt_gbH (S : InaccSeq.{0}) (j k : ℕ) : gaG j < gbH k := (gaG_lt_W S j).trans_le (gaW_le_gbH S k)

/-- **`ψ_{Ω₂}(ω·2) = gbV`**: strongly critical, above every `gbH k`. -/
theorem gbV_psi (S : InaccSeq.{0}) : S.psi (ω * 2) (Om (1 + 1)) = gbV ∧ SC gbV ∧ ∀ k : ℕ, gbH k < gbV := by
  have hω2 : (ω : Ordinal.{0}) * 2 = ω + ω := mul_two_eq ω
  have hlt : ∀ k : ℕ, gbH k < S.psi (ω * 2) (Om (1 + 1)) := fun k => by
    rw [← (gbH_spec S k).1]
    exact psi_lt_psi_of_mem (InR_Om_succ 1)
      (by rw [hω2]; exact (add_lt_add_iff_left _).2 (natCast_lt_omega0 k)) (gb_off_mem _ _ k)
  have hin : S.psi (ω * 2) (Om (1 + 1)) ∈ {b | SC b ∧ ∀ k : ℕ, gbH k < b} := ⟨ga_psi_SC _, hlt⟩
  have hne : {b | SC b ∧ ∀ k : ℕ, gbH k < b}.Nonempty := ⟨_, hin⟩
  have hmem : gbV ∈ {b | SC b ∧ ∀ k : ℕ, gbH k < b} := csInf_mem hne
  have hle : gbV ≤ S.psi (ω * 2) (Om (1 + 1)) := csInf_le' hin
  have hge : S.psi (ω * 2) (Om (1 + 1)) ≤ gbV := by
    refine gaPsi_le S hmem.1 ((gbH_Om1_lt S 0).trans (hmem.2 0)) fun e he => ?_
    rw [hω2] at he
    obtain ⟨n, hn⟩ : ∃ n : ℕ, e ≤ ω + (n : Ordinal.{0}) := by
      rcases lt_or_ge e ω with heω | heω
      · exact ⟨0, by rw [Nat.cast_zero, add_zero]; exact heω.le⟩
      · have hd : ω + (e - ω) = e := Ordinal.add_sub_cancel_of_le heω
        have hd' : e - ω < ω := (add_lt_add_iff_left ω).1 (by rw [hd]; exact he)
        obtain ⟨n, hn⟩ := lt_omega0.1 hd'
        exact ⟨n, by rw [← hn, hd]⟩
    exact ((psi_mono (InR_Om_succ 1) hn).1.trans_eq (gbH_spec S n).1).trans_lt (hmem.2 n)
  exact ⟨le_antisymm hge hle, hmem.1, hmem.2⟩

theorem gbV_SC (S : InaccSeq.{0}) : SC gbV := (gbV_psi S).2.1

theorem gbH_lt_V (S : InaccSeq.{0}) (k : ℕ) : gbH k < gbV := (gbV_psi S).2.2 k

theorem gbV_le {b : Ordinal.{0}} (hb : SC b) (h : ∀ k : ℕ, gbH k < b) : gbV ≤ b :=
  csInf_le' (s := {b | SC b ∧ ∀ k : ℕ, gbH k < b}) ⟨hb, h⟩

theorem gbV_lt_Om2 (S : InaccSeq.{0}) : gbV < Om (1 + 1) := by
  rw [← (gbV_psi S).1]; exact psi_lt (InR_Om_succ 1) _

theorem ga_Om1_lt_V (S : InaccSeq.{0}) : Om 1 < gbV := (gbH_Om1_lt S 0).trans (gbH_lt_V S 0)

theorem gaW_lt_V (S : InaccSeq.{0}) : gaW < gbV := gbH_lt_V S 0

/-- **`gbV = sup_k gbH k`.** -/
theorem gbV_sup (S : InaccSeq.{0}) : gbV = ⨆ k : ℕ, gbH k := by
  have hbdd : BddAbove (range gbH) := Ordinal.bddAbove_of_small
  have hle1 : ∀ k : ℕ, gbH k < ⨆ k : ℕ, gbH k := fun k =>
    (gbH_lt_succ S k).trans_le (le_ciSup hbdd (k + 1))
  refine le_antisymm (gbV_le ⟨lt_of_le_of_lt zero_le (hle1 0), fun x hx y hy => ?_⟩ hle1)
    (ciSup_le' fun k => (gbH_lt_V S k).le)
  obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 hx
  obtain ⟨m, hm⟩ := (lt_ciSup_iff hbdd).1 hy
  have h1 : x < gbH (max n m) := hn.trans_le ((gbH_strictMono S).monotone (le_max_left n m))
  have h2 : y < gbH (max n m) := hm.trans_le ((gbH_strictMono S).monotone (le_max_right n m))
  exact ((gbH_SC S _).2 x h1 y h2).trans (hle1 _)

/-- **Every strongly critical `s` with `Ω₁ < s < gbV` is an atom.** -/
theorem gbSC_cases {s : Ordinal.{0}} (hs : SC s) (h1 : Om 1 < s) (h2 : s < gbV) : s ∈ gbAt := by
  rcases lt_or_ge s gaW with hW | hW
  · obtain ⟨k, hk⟩ := gaSC_cases hs h1 hW
    exact Or.inl ⟨k, hk⟩
  · refine Or.inr ?_
    by_contra hne
    push Not at hne
    have hall : ∀ k : ℕ, gbH k < s := by
      intro k
      induction k with
      | zero => exact lt_of_le_of_ne hW (hne 0).symm
      | succ k ih => exact lt_of_le_of_ne (gbH_succ_le hs ih) (hne (k + 1)).symm
    exact absurd (gbV_le hs hall) (not_le.2 h2)

/-- The atoms are strongly critical and above `Ω₁`. -/
theorem gbAt_GxAt (S : InaccSeq.{0}) : GxAt gbAt := by
  rintro s (⟨k, rfl⟩ | ⟨k, rfl⟩)
  · exact ⟨gaG_SC S k, gaG_Om1_lt S k⟩
  · exact ⟨gbH_SC S k, gbH_Om1_lt S k⟩

theorem gbAt_lt_V (S : InaccSeq.{0}) {s : Ordinal.{0}} (hs : s ∈ gbAt) : s < gbV := by
  rcases hs with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact (gaG_lt_gbH S k 0).trans (gbH_lt_V S 0)
  · exact gbH_lt_V S k

/-- `gbH k ∈ Cl(a, b)` for `ω + k < a`. -/
theorem gbH_mem {a b : Ordinal.{0}} {k : ℕ} (hk : ω + (k : Ordinal.{0}) < a) : gbH k ∈ S.CSet a b := by
  rw [← (gbH_spec S k).1]
  exact CSet.psi_mem hk (InR_Om_succ 1) (ga_Om2_mem _ _) (gb_off_mem _ _ k)

theorem gb_omega_le_two : (ω : Ordinal.{0}) ≤ ω * 2 := by rw [mul_two_eq]; exact le_self_add

theorem gbAt_mem {a b s : Ordinal.{0}} (ha : ω * 2 ≤ a) (hs : s ∈ gbAt) : s ∈ S.CSet a b := by
  rcases hs with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact gaG_mem ((natCast_lt_omega0 k).trans_le (gb_omega_le_two.trans ha))
  · refine gbH_mem (lt_of_lt_of_le ?_ ha)
    rw [mul_two_eq]; exact (add_lt_add_iff_left _).2 (natCast_lt_omega0 k)

theorem gb_A_ge (η : Ordinal.{0}) : ω * 2 ≤ ConjT.Aη S η := by
  have h1 : (ω : Ordinal.{0}) < Om ω := omega0_lt_Om omega0_ne_zero
  have h2 : (ω : Ordinal.{0}) * 2 < Om ω := by
    rw [mul_two_eq]; exact (SC_Om omega0_ne_zero).isPrincipal h1 h1
  exact h2.le.trans le_self_add

/-! ## The codes -/

variable {Z y : Ordinal.{0}}

/-- **A code over `Z ≤ Ω₁` is below `Γ_{Ω₁+ω·2}`.** -/
theorem gbCl_lt_V (S : InaccSeq.{0}) (hZ : Z ≤ Om 1) {c : Ordinal.{0}} (hc : GxCl Z gbAt c) : c < gbV := by
  have hSC := gbV_SC S
  induction hc with
  | small h => exact (h.trans_le hZ).trans (ga_Om1_lt_V S)
  | om => exact ga_Om1_lt_V S
  | atom hs => exact gbAt_lt_V S hs
  | add _ _ ihx ihy => exact hSC.isPrincipal ihx ihy
  | phi _ _ ihx ihy => exact hSC.2 _ ihx _ ihy

/-- **A code lies in every hull `Cl(a, b)` with `ω·2 ≤ a` and `Z ≤ b`.** -/
theorem gbCl_mem_CSet {a b : Ordinal.{0}} (ha : ω * 2 ≤ a) (hZb : Z ≤ b) {x : Ordinal.{0}}
    (hx : GxCl Z gbAt x) : x ∈ S.CSet a b := by
  induction hx with
  | small h => exact CSet.of_lt (lt_of_lt_of_le h hZb)
  | om => exact CSet.Om_mem (CSet.one_mem _ _)
  | atom hs => exact gbAt_mem ha hs
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-- **The hull below `Γ_{Ω₁+ω·2}` consists of codes**: if every countable member of `Cl(a, Z)` is below `Z`, every
member of `Cl(a, Z)` below `gbV` is a code over `Z`. -/
theorem gbCl_of_CSet {a : Ordinal.{0}} (hZ : 0 < Z) (hkey : ∀ y ∈ S.CSet a Z, y < Om 1 → y < Z) :
    ∀ x ∈ S.CSet a Z, x < gbV → GxCl Z gbAt x := by
  intro x hx
  have hx' := hx
  have hG2 := (gbV_lt_Om2 S).le
  induction hx with
  | small h => exact fun _ => GxCl.small h
  | zero => exact fun _ => GxCl.zero hZ
  | inacc n =>
    intro h
    exact absurd ((h.trans_le hG2).trans (mxOm2_lt_I n)) (lt_irrefl _)
  | inaccW =>
    intro h
    exact absurd ((h.trans_le hG2).trans mxOm2_lt_Iw) (lt_irrefl _)
  | @add x y hx1 hy1 ihx ihy =>
    intro h
    exact GxCl.add (ihx hx1 (lt_of_le_of_lt le_self_add h)) (ihy hy1 (lt_of_le_of_lt le_add_self h))
  | @phi x y hx1 hy1 ihx ihy =>
    intro h
    exact GxCl.phi (ihx hx1 (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy hy1 (lt_of_le_of_lt (right_le_veblen x y) h))
  | @om x hx1 _ =>
    intro h
    have h2 : x < 1 + 1 := Om_lt_Om.1 (h.trans_le hG2)
    rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
    · rw [Order.lt_one_iff] at h0; rw [h0, Om_zero]; exact GxCl.zero hZ
    · rw [h1]; exact GxCl.om
  | @coll π e hπ hπ1 he1 _ _ =>
    intro h
    by_cases hπ0 : π = Om 1
    · have hlt : S.psi e.1 π < Om 1 := by rw [hπ0]; exact psi_lt Low.InR_Om_one _
      exact GxCl.small (hkey _ hx' hlt)
    · have hge : Om 1 ≤ S.psi e.1 π := not_lt.1 fun h' => hπ0 (Low.eq_Om_one_of_psi_lt hπ h')
      have hne : Om 1 ≠ S.psi e.1 π := fun h' =>
        psi_notMem hπ e.1 (h' ▸ CSet.Om_mem (CSet.one_mem _ _))
      exact GxCl.atom (gbSC_cases (SC_psi hπ _) (lt_of_le_of_ne hge hne) h)

/-- **Below `Γ_{Ω₁+ω}` a code with the atoms `gbAt` is a code with the atoms `gaAt`.** -/
theorem ga_of_gbCl (S : InaccSeq.{0}) {x : Ordinal.{0}} (hx : GxCl Z gbAt x) : x < gaW → GxCl Z gaAt x := by
  induction hx with
  | small h => exact fun _ => GxCl.small h
  | om => exact fun _ => GxCl.om
  | @atom s hs =>
    intro h
    rcases hs with hs | ⟨k, rfl⟩
    · exact GxCl.atom hs
    · exact absurd h (not_lt.2 (gaW_le_gbH S k))
  | @add x y _ _ ihx ihy =>
    exact fun h => GxCl.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => GxCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))

theorem gb_of_gaCl {x : Ordinal.{0}} (hx : GxCl Z gaAt x) : GxCl Z gbAt x := hx.mono le_rfl gaAt_sub_gbAt

/-- **`Θ_y(c)` with the atoms `gbAt` is `Θ_y(c)` with the atoms `gaAt` for `c ≤ Γ_{Ω₁+ω}`.** -/
theorem gbTh_eq_gaTh (S : InaccSeq.{0}) {c : Ordinal.{0}} (hc : c ≤ gaW) : gxTh y gbAt c = gxTh y gaAt c :=
  ggOtp_congr c fun _ hx => ⟨fun h => ga_of_gbCl S h (hx.trans_le hc), fun h => gb_of_gaCl h⟩

/-- **`Θ_y(Γ_{Ω₁+ω}) = sup_k Θ_y(Γ_{Ω₁+1+k})`.** -/
theorem gbTh_W (S : InaccSeq.{0}) : gxTh y gbAt gaW = ⨆ k : ℕ, gxTh y gaAt (gaG k) := by
  rw [gbTh_eq_gaTh S le_rfl]
  conv_lhs => rw [gaW_sup S]
  exact gxTh_iSup gaG

theorem gbTh_gaG (S : InaccSeq.{0}) (k : ℕ) : gxTh y gbAt (gaG k) = gxTh y gaAt (gaG k) :=
  gbTh_eq_gaTh S (gaG_lt_W S k).le

/-- **The reading of `gbH k` is strongly critical, above `y`, below `Ω₁`.** -/
theorem gbTh_H (S : InaccSeq.{0}) (hy : SC y) (hy1 : y < Om 1) :
    ∀ k : ℕ, SC (gxTh y gbAt (gbH k)) ∧ y < gxTh y gbAt (gbH k) ∧ gxTh y gbAt (gbH k) < Om 1
  | 0 => by
    have hAt := gbAt_GxAt S
    refine ⟨gxTh_SC hy hAt (gaW_SC S) (hy1.trans (ga_Om1_lt_W S)), ?_, ?_⟩
    · have h1 := (gaTh_G S hy hy1 0).2.1
      rw [← gbTh_gaG S 0] at h1
      exact h1.trans_le (gxTh_mono (gaG_lt_W S 0).le)
    · show gxTh y gbAt gaW < Om 1
      rw [gbTh_W S, ← ph_Om1_eq]
      exact Ordinal.iSup_lt_omega_one fun k => by
        have := (gaTh_G S hy hy1 k).2.2
        rw [← ph_Om1_eq] at this
        exact this
  | k + 1 => by
    obtain ⟨ihS, ihy, ih1⟩ := gbTh_H S hy hy1 k
    have hAt := gbAt_GxAt S
    have hXS := Lp.lpG_SC ihS ih1
    obtain ⟨hX1, hX2⟩ := Lp.lpG_facts ihS ih1
    have hle : gxTh y gbAt (gbH (k + 1)) ≤ lgG (gxTh y gbAt (gbH k)) := by
      refine Ld.ldAtom_le hy hy1 hAt hXS (ihy.trans hX1) fun t ht htk => ?_
      have htle : t ≤ gbH k := by
        rcases ht with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · exact (gaG_lt_gbH S j k).le
        · exact (gbH_strictMono S).monotone (Nat.lt_succ_iff.1 ((gbH_strictMono S).lt_iff_lt.1 htk))
      exact (gxTh_mono htle).trans_lt hX1
    have hlt : gxTh y gbAt (gbH k) < gxTh y gbAt (gbH (k + 1)) :=
      gxTh_lt (GxCl.atom (Or.inr ⟨k, rfl⟩)) (gbH_lt_succ S k)
    exact ⟨gxTh_SC hy hAt (gbH_SC S _) (hy1.trans (gbH_Om1_lt S _)), ihy.trans hlt, hle.trans_lt hX2⟩

/-- **The reading of every atom is strongly critical, above `y`, below `Ω₁`.** -/
theorem gbTh_At (S : InaccSeq.{0}) (hy : SC y) (hy1 : y < Om 1) {s : Ordinal.{0}} (hs : s ∈ gbAt) :
    SC (gxTh y gbAt s) ∧ y < gxTh y gbAt s ∧ gxTh y gbAt s < Om 1 := by
  rcases hs with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [gbTh_gaG S k]; exact gaTh_G S hy hy1 k
  · exact gbTh_H S hy hy1 k

/-- Every reading of a code over `y` is below `Ω₁`. -/
theorem gbTh_lt_Om1 (S : InaccSeq.{0}) (hy : SC y) (hy1 : y < Om 1) {c : Ordinal.{0}} (hc : GxCl y gbAt c) :
    gxTh y gbAt c < Om 1 := by
  have hAt := gbAt_GxAt S
  induction hc with
  | small h => rw [gxTh_small h.le]; exact h.trans hy1
  | om => rw [gxTh_Om1 hy hy1 hAt]; exact hy1
  | atom hs => exact (gbTh_At S hy hy1 hs).2.2
  | @add u v hu _ ihu ihv => rw [gxTh_add hy hAt hu]; exact ph_SC_Om1.isPrincipal ihu ihv
  | @phi a b ha hb iha ihb => rw [gxTh_phi hy hAt a ha b hb]; exact ph_SC_Om1.2 _ iha _ ihb

/-! ## Terms for the codes -/

/-- **Terms for the codes below `E`** (atoms `gbAt`): for every code `c < E` over `Z` some term of `X` has the value
`Θ_y(c)` at every strongly critical `y < Ω₁` with `Z ≤ y`. -/
def GbPoly (X : XtSys) (E : Ordinal.{0}) : Prop :=
  ∀ Z c, GxCl Z gbAt c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
    X.CB s y ∧ X.val s y = gxTh y gbAt c

/-- **Reduction to strongly critical `Z`.** -/
theorem gbPoly_of_SC {X : XtSys} {E : Ordinal.{0}}
    (h : ∀ Z, SC Z → Z < Om 1 → ∀ c, GxCl Z gbAt c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
      X.CB s y ∧ X.val s y = gxTh y gbAt c) : GbPoly X E := by
  intro Z c hc hcE
  by_cases hex : ∃ y, SC y ∧ y < Om 1 ∧ Z ≤ y
  · have hmem : sInf {y | SC y ∧ y < Om 1 ∧ Z ≤ y} ∈ {y | SC y ∧ y < Om 1 ∧ Z ≤ y} := csInf_mem hex
    obtain ⟨h1, h2, h3⟩ := hmem
    obtain ⟨s, hs⟩ := h _ h1 h2 c (hc.mono h3 Subset.rfl) hcE
    exact ⟨s, fun y hy hy1 hZy => hs y hy hy1 (csInf_le' ⟨hy, hy1, hZy⟩)⟩
  · push Not at hex
    exact ⟨X.cst 0, fun y hy hy1 hZy => absurd hZy (not_le.2 (hex y hy hy1))⟩

/-- **`GaPoly X E` with `E ≤ Γ_{Ω₁+ω}` gives `GbPoly X E`.** -/
theorem gbPoly_of_ga (S : InaccSeq.{0}) {X : XtSys} {E : Ordinal.{0}} (hE : E ≤ gaW) (h : GaPoly X E) :
    GbPoly X E := by
  intro Z c hc hcE
  obtain ⟨s, hs⟩ := h Z c (ga_of_gbCl S hc (hcE.trans_le hE)) hcE
  refine ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1, ?_⟩⟩
  rw [(hs y hy hy1 hZy).2, gbTh_eq_gaTh S (hcE.trans_le hE).le]

end Googology.Trans.PoR.InaccPsi.R2.Gb
