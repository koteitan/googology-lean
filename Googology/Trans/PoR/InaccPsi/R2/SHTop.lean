import Googology.Trans.PoR.InaccPsi.R2.SHDeep

/-!
# Theorem SH in `R₂^C`: the tops and restarts of a level

For a level `k ≥ 1` the sequence `β^k` (`shBeta k`) is `β^k_0 = T_k`, `β^k_{g+1} = T_k(β^k_g)` and
`β^k_l = sup_{g<l} β^k_g` at limits `l`.  Below `T_ω` (`shTw`, `R2.SHDeep`) its values at `0` and at
successors are the **level-`k` tops** (`shTop k`), its values at limits the **level-`k` restarts**
(`shRes k`).  `shNestCof k p`: `k`-nests are cofinal below `p` (for every `c < p` some `k`-nest lies in
`(c, p)`).  `U_k(ξ) = {u ∈ (ξ, T_k(ξ)] : u ≤₁ T_k(ξ)}` and `Y_k = Res_k ∪ ⋃_{ξ<T_ω} U_k(ξ)` (`shY k`).

* `shBeta_strict` (`β^k` is strictly increasing below `T_ω`), `shBeta_unbdd` (it reaches `T_ω`),
  `shBeta_Tw` (`T_ω = β^k_l` for a limit `l`: `T_ω` is a limit of level-`k` tops for every `k`);
* `shExhaust` (**the level-`k` tops and restarts exhaust `[0, T_ω)`**: every `ξ < T_ω` is below `T_k` or
  lies in `[p, T_k(p))` for a top or restart `p`, and `T_k(p)` is a top);
* `shReachPast` (**only restarts of level `k` reach past a level-`k` top above them**);
* `shRes_iff` (`p ∈ Res_k` iff `0 < p < T_ω` and `k`-nests are cofinal below `p`);
* `shNoCross` (**no pair of depth `≤ k` crosses `Top_k ∪ Res_k`**: a pair `x <₂ y` with a
  point of `Top_k ∪ Res_k` in `(x, y)` is the outer pair of a `(k+1)`-nest);
* `shTop_sub_res`, `shRes_sub_res`, `shU_sub_res`, `shLeft_sub_res`, `shY_sub_res` (**the level-`(k+1)`
  tops and restarts, every `U_{k+1}(ξ)`, the left ends of pairs of depth `k + 1`, hence `Y_{k+1}`, lie in
  `Res_k`**), `shRes_sub_Y` (`Res_k ⊆ Y_k`).

The cofinality of nests below a `<₂`-right end uses [C09] Def 5.3 clause 2 of `≤₂` as in NEST-UP.
No new axiom.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-! ## The sequence `β^k` -/

/-- `β^k_g`: `β^k_0 = T_k`, `β^k_{g+1} = T_k(β^k_g)`, `β^k_l = sup_{g<l} β^k_g` at limits. -/
noncomputable def shBeta (k : ℕ) (g : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.limitRecOn (motive := fun _ => Ordinal.{0}) g (Tk k) (fun _ b => TkA b k)
    (fun l _ IH => ⨆ g : Set.Iio l, IH g.1 g.2)

theorem shBeta_zero (k : ℕ) : shBeta k 0 = Tk k := by
  unfold shBeta; exact limitRecOn_zero ..

theorem shBeta_succ (k : ℕ) (g : Ordinal.{0}) : shBeta k (g + 1) = TkA (shBeta k g) k := by
  unfold shBeta; rw [limitRecOn_add_one]

theorem shBeta_limit (k : ℕ) {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    shBeta k l = ⨆ g : Set.Iio l, shBeta k g.1 := by
  unfold shBeta; rw [limitRecOn_limit _ _ _ _ hl]

theorem shBeta_bdd (k : ℕ) (l : Ordinal.{0}) :
    BddAbove (Set.range fun g : Set.Iio l => shBeta k g.1) :=
  Ordinal.bddAbove_of_small

/-- **Level-`k` tops**: `β^k_0` and the `β^k_{s+1}` below `T_ω`. -/
def shTop (k : ℕ) (t : Ordinal.{0}) : Prop :=
  t < shTw ∧ (t = shBeta k 0 ∨ ∃ s, t = shBeta k (s + 1))

/-- **Level-`k` restarts**: the `β^k_l` (`l` a limit) below `T_ω`. -/
def shRes (k : ℕ) (t : Ordinal.{0}) : Prop :=
  t < shTw ∧ ∃ l, IsSuccLimit l ∧ t = shBeta k l

/-- `k`-nests are cofinal below `p`. -/
def shNestCof (k : ℕ) (p : Ordinal.{0}) : Prop :=
  ∀ c < p, ∃ a b, NestSeq k a b ∧ c < a 0 ∧ b 0 < p

/-- `Y_k = Res_k ∪ ⋃_{ξ<T_ω} U_k(ξ)`, `U_k(ξ) = {u ∈ (ξ, T_k(ξ)] : u ≤₁ T_k(ξ)}`. -/
def shY (k : ℕ) (u : Ordinal.{0}) : Prop :=
  shRes k u ∨ ∃ ξ < shTw, ξ < u ∧ u ≤ TkA ξ k ∧ le1 u (TkA ξ k)

section Seq

variable (m : ℕ)

theorem shBeta_succ_lt {s : Ordinal.{0}} (hW : shBeta (m + 1) (s + 1) < shTw) :
    shBeta (m + 1) s < shBeta (m + 1) (s + 1) := by
  have h1 : TkA (shBeta (m + 1) s) (m + 1) < Om1 := by
    rw [← shBeta_succ]; exact hW.trans shTw_lt_Om1
  obtain ⟨a, b, hN, hξ, hT⟩ := TkA_attained h1
  rw [shBeta_succ, ← hT]
  exact hξ.trans (lv_xT hN)

/-- **`β^k` is strictly increasing below `T_ω`.** -/
theorem shBeta_strict (g : Ordinal.{0}) :
    shBeta (m + 1) g < shTw → ∀ g' < g, shBeta (m + 1) g' < shBeta (m + 1) g := by
  induction g using Ordinal.limitRecOn with
  | zero => intro _ g' hg'; exact absurd hg' (not_lt.2 zero_le)
  | add_one s ih =>
    intro hW g' hg'
    have hs := shBeta_succ_lt m hW
    rcases lt_or_eq_of_le (Order.lt_add_one_iff.1 hg') with h | h
    · exact (ih (hs.trans hW) g' h).trans hs
    · rw [h]; exact hs
  | limit l hl ih =>
    intro hW g' hg'
    have hg1 : g' + 1 < l := hl.add_one_lt hg'
    have hle : shBeta (m + 1) (g' + 1) ≤ shBeta (m + 1) l := by
      rw [shBeta_limit _ hl]
      exact le_ciSup (shBeta_bdd _ l) (⟨g' + 1, hg1⟩ : Set.Iio l)
    exact lt_of_lt_of_le
      (ih (g' + 1) hg1 (lt_of_le_of_lt hle hW) g' (Order.lt_add_one_iff.2 le_rfl)) hle

theorem shBeta_mono {g g' : Ordinal.{0}} (hW : shBeta (m + 1) g < shTw) (hg : g' ≤ g) :
    shBeta (m + 1) g' ≤ shBeta (m + 1) g := by
  rcases eq_or_lt_of_le hg with rfl | h
  · exact le_rfl
  · exact (shBeta_strict m g hW g' h).le

/-- **`β^k` reaches `T_ω`.** -/
theorem shBeta_unbdd : ∃ g, shTw ≤ shBeta (m + 1) g := by
  by_contra h
  push Not at h
  have hsm : StrictMono (shBeta (m + 1)) := fun g' g hg => shBeta_strict m g (h g) g' hg
  exact absurd (h shTw) (not_lt.2 hsm.le_apply)

theorem shBeta_exhaust {ξ : Ordinal.{0}} (hξ : ξ < shTw) :
    ξ < shBeta (m + 1) 0 ∨ ∃ s, shBeta (m + 1) s ≤ ξ ∧ ξ < shBeta (m + 1) (s + 1) := by
  obtain ⟨g, hg⟩ := shBeta_unbdd m
  set S : Set Ordinal.{0} := {g | ξ < shBeta (m + 1) g} with hS
  have hne : S.Nonempty := ⟨g, lt_of_lt_of_le hξ hg⟩
  have hmem : ξ < shBeta (m + 1) (sInf S) := csInf_mem hne
  have hmin : ∀ g' < sInf S, shBeta (m + 1) g' ≤ ξ := fun g' h =>
    not_lt.1 fun h' => absurd (csInf_le (OrderBot.bddBelow S) h') (not_le.2 h)
  rcases zero_or_succ_or_isSuccLimit (sInf S) with h0 | ⟨s, hs⟩ | hl
  · left; rw [h0] at hmem; exact hmem
  · right
    refine ⟨s, hmin s ?_, ?_⟩
    · rw [← hs]; exact Order.lt_succ s
    · have he : s + 1 = sInf S := by rw [← hs, Order.succ_eq_add_one]
      rw [he]; exact hmem
  · exfalso
    have h0 : 0 < sInf S := by rw [← Ordinal.bot_eq_zero]; exact hl.bot_lt
    haveI : Nonempty (Set.Iio (sInf S)) := ⟨⟨0, h0⟩⟩
    rw [shBeta_limit _ hl] at hmem
    obtain ⟨⟨g', hg'⟩, hlt⟩ := (lt_ciSup_iff (shBeta_bdd _ _)).1 hmem
    exact absurd (hmin g' hg') (not_le.2 hlt)

/-- **`T_ω = β^k_l` for a limit `l`**: `T_ω` is a limit of level-`k` tops, for every `k`. -/
theorem shBeta_Tw : ∃ l, IsSuccLimit l ∧ shBeta (m + 1) l = shTw := by
  obtain ⟨g, hg⟩ := shBeta_unbdd m
  set S : Set Ordinal.{0} := {g | shTw ≤ shBeta (m + 1) g} with hS
  have hne : S.Nonempty := ⟨g, hg⟩
  have hmem : shTw ≤ shBeta (m + 1) (sInf S) := csInf_mem hne
  have hmin : ∀ g' < sInf S, shBeta (m + 1) g' < shTw := fun g' h =>
    not_le.1 fun h' => absurd (csInf_le (OrderBot.bddBelow S) h') (not_le.2 h)
  rcases zero_or_succ_or_isSuccLimit (sInf S) with h0 | ⟨s, hs⟩ | hl
  · rw [h0, shBeta_zero] at hmem
    exact absurd hmem (not_le.2 (shTk_lt_Tw m))
  · have he : s + 1 = sInf S := by rw [← hs, Order.succ_eq_add_one]
    have hsW := hmin s (by rw [← hs]; exact Order.lt_succ s)
    rw [← he, shBeta_succ] at hmem
    exact absurd hmem (not_le.2 (shTkA_lt_Tw hsW m))
  · have h0 : 0 < sInf S := by rw [← Ordinal.bot_eq_zero]; exact hl.bot_lt
    haveI : Nonempty (Set.Iio (sInf S)) := ⟨⟨0, h0⟩⟩
    refine ⟨sInf S, hl, le_antisymm ?_ hmem⟩
    rw [shBeta_limit _ hl]
    exact ciSup_le fun g' => (hmin g'.1 g'.2).le

/-- A top below `T_ω` is some `β^k_g`. -/
theorem shTop_beta {t : Ordinal.{0}} (ht : shTop (m + 1) t) : ∃ g, t = shBeta (m + 1) g := by
  rcases ht.2 with h | ⟨s, h⟩
  · exact ⟨0, h⟩
  · exact ⟨s + 1, h⟩

/-- **A level-`k` top is the top of a `k`-nest.** -/
theorem shTop_nest {t : Ordinal.{0}} (ht : shTop (m + 1) t) :
    ∃ a b, NestSeq (m + 1) a b ∧ b 0 = t := by
  rcases ht.2 with h | ⟨s, h⟩
  · rw [shBeta_zero] at h
    obtain ⟨a, b, hN, hT⟩ := Tk_attained (Tk_lt_Om1_all (k := m + 1) (by omega))
    exact ⟨a, b, hN, hT.trans h.symm⟩
  · rw [shBeta_succ] at h
    obtain ⟨a, b, hN, -, hT⟩ := TkA_attained (h ▸ ht.1.trans shTw_lt_Om1)
    exact ⟨a, b, hN, hT.trans h.symm⟩

/-- **The level-`k` tops and restarts exhaust `[0, T_ω)`**: every `ξ < T_ω` is below `T_k` or lies in
`[p, T_k(p))` for a level-`k` top or restart `p`, and then `T_k(p)` is a level-`k` top. -/
theorem shExhaust {ξ : Ordinal.{0}} (hξ : ξ < shTw) :
    ξ < Tk (m + 1) ∨ ∃ p, (shTop (m + 1) p ∨ shRes (m + 1) p) ∧ p ≤ ξ ∧ ξ < TkA p (m + 1) ∧
      shTop (m + 1) (TkA p (m + 1)) := by
  rcases shBeta_exhaust m hξ with h | ⟨s, h1, h2⟩
  · left; rwa [shBeta_zero] at h
  · right
    have hpW : shBeta (m + 1) s < shTw := lt_of_le_of_lt h1 hξ
    have hnW : TkA (shBeta (m + 1) s) (m + 1) < shTw := shTkA_lt_Tw hpW m
    refine ⟨shBeta (m + 1) s, ?_, h1, by rwa [← shBeta_succ], hnW, Or.inr ⟨s, (shBeta_succ _ _).symm⟩⟩
    rcases zero_or_succ_or_isSuccLimit s with h0 | ⟨s', hs'⟩ | hl
    · exact Or.inl ⟨hpW, Or.inl (by rw [h0])⟩
    · exact Or.inl ⟨hpW, Or.inr ⟨s', by rw [← hs', Order.succ_eq_add_one]⟩⟩
    · exact Or.inr ⟨hpW, s, hl, rfl⟩

/-- **Only restarts of level `k` reach past a level-`k` top above them.** -/
theorem shReachPast {α t g' : Ordinal.{0}} (hαt : α < t) (ht : shTop (m + 1) t) (htg : t < g')
    (h1 : le1 α g') : shRes (m + 1) α := by
  obtain ⟨g, rfl⟩ := shTop_beta m ht
  have hαW : α < shTw := hαt.trans ht.1
  have hT0 : Tk (m + 1) ≤ shBeta (m + 1) g := by
    rw [← shBeta_zero]; exact shBeta_mono m ht.1 zero_le
  obtain ⟨a0, b0, hN0, hT0'⟩ := Tk_attained (Tk_lt_Om1_all (k := m + 1) (by omega))
  rcases shBeta_exhaust m hαW with h | ⟨s, hs1, hs2⟩
  · rw [shBeta_zero] at h
    exact absurd h1 (cap_Tk (by omega) hN0 hT0' α h.le g' (lt_of_le_of_lt hT0 htg))
  · have hsW : shBeta (m + 1) s < shTw := lt_of_le_of_lt hs1 hαW
    have hsg : shBeta (m + 1) (s + 1) ≤ shBeta (m + 1) g := by
      apply shBeta_mono m ht.1
      by_contra hgs
      push Not at hgs
      have := shBeta_mono m hsW (Order.lt_add_one_iff.1 hgs)
      exact absurd (lt_of_lt_of_le hαt this) (not_lt.2 hs1)
    rcases eq_or_lt_of_le hs1 with he | hlt
    · rcases zero_or_succ_or_isSuccLimit s with h0 | ⟨s', hs'⟩ | hl
      · rw [h0, shBeta_zero] at he
        exact absurd h1 (cap_Tk (by omega) hN0 hT0' α he.ge g' (he ▸ hαt.trans htg))
      · rw [← hs', Order.succ_eq_add_one] at he
        have hlt' := shBeta_succ_lt m (he ▸ hαW)
        rw [shBeta_succ] at he hlt'
        obtain ⟨a, b, hN, hξ, hT⟩ := TkA_attained (he ▸ hαW.trans shTw_lt_Om1)
        exact absurd h1 (capA (by omega) hN hξ hT α (he ▸ hlt') (hT ▸ he.ge) g'
          (hT ▸ he ▸ hαt.trans htg))
      · exact ⟨hαW, s, hl, he.symm⟩
    · have hnW : shBeta (m + 1) (s + 1) < shTw := lt_of_le_of_lt hsg ht.1
      rw [shBeta_succ] at hs2 hsg hnW
      obtain ⟨a, b, hN, hξ, hT⟩ := TkA_attained (hnW.trans shTw_lt_Om1)
      exact absurd h1 (capA (by omega) hN hξ hT α hlt (hT ▸ hs2.le) g'
        (hT ▸ lt_of_le_of_lt hsg htg))

/-- **`p ∈ Res_k` iff `0 < p < T_ω` and `k`-nests are cofinal below `p`.** -/
theorem shRes_iff {p : Ordinal.{0}} :
    shRes (m + 1) p ↔ p < shTw ∧ 0 < p ∧ shNestCof (m + 1) p := by
  constructor
  · rintro ⟨hpW, l, hl, rfl⟩
    have h0l : 0 < l := by rw [← Ordinal.bot_eq_zero]; exact hl.bot_lt
    refine ⟨hpW, lt_of_le_of_lt zero_le (shBeta_strict m l hpW 0 h0l), fun c hc => ?_⟩
    have hc' := hc
    haveI : Nonempty (Set.Iio l) := ⟨⟨0, h0l⟩⟩
    rw [shBeta_limit _ hl] at hc'
    obtain ⟨⟨g, hg⟩, hcg⟩ := (lt_ciSup_iff (shBeta_bdd _ _)).1 hc'
    have hg1 : g + 1 < l := hl.add_one_lt hg
    have hlt := shBeta_strict m l hpW (g + 1) hg1
    rw [shBeta_succ] at hlt
    obtain ⟨a, b, hN, hξ, hT⟩ := TkA_attained (hlt.trans (hpW.trans shTw_lt_Om1))
    exact ⟨a, b, hN, hcg.trans hξ, hT ▸ hlt⟩
  · rintro ⟨hpW, hp0, hcof⟩
    obtain ⟨a0, b0, hN0, hb0⟩ := hcof 0 hp0
    have hTp : Tk (m + 1) < p := lt_of_le_of_lt (Tk_le hN0) hb0.2
    rcases shBeta_exhaust m hpW with h | ⟨s, hs1, hs2⟩
    · rw [shBeta_zero] at h; exact absurd hTp (not_lt.2 h.le)
    · rcases eq_or_lt_of_le hs1 with he | hlt
      · rcases zero_or_succ_or_isSuccLimit s with h0 | ⟨s', hs'⟩ | hl
        · rw [h0, shBeta_zero] at he; exact absurd hTp (not_lt.2 he.ge)
        · rw [← hs', Order.succ_eq_add_one] at he
          have hlt' := shBeta_succ_lt m (he ▸ hpW)
          rw [he] at hlt'
          obtain ⟨a, b, hN, hξ, hb⟩ := hcof _ hlt'
          have := TkA_le hN hξ
          rw [← shBeta_succ, he] at this
          exact absurd (lt_of_le_of_lt this hb) (lt_irrefl _)
        · exact ⟨hpW, s, hl, he.symm⟩
      · obtain ⟨a, b, hN, hξ, hb⟩ := hcof _ hlt
        have := TkA_le hN hξ
        rw [← shBeta_succ] at this
        exact absurd (lt_of_le_of_lt this hb) (not_lt.2 hs2.le)

/-- **No pair of depth `≤ k` crosses `Top_k ∪ Res_k`**: a pair `x <₂ y` with a point of
`Top_k ∪ Res_k` strictly between `x` and `y` is the outer pair of a `(k+1)`-nest. -/
theorem shNoCross {x y p : Ordinal.{0}} (hxy : x < y) (h2 : le2 x y)
    (hp : shTop (m + 1) p ∨ shRes (m + 1) p) (hxp : x < p) (hpy : p < y) :
    ∃ a b, NestSeq (m + 1 + 1) a b ∧ a 0 = x ∧ b 0 = y := by
  have hin : ∃ a b, NestSeq (m + 1) a b ∧ x < a 0 ∧ b 0 < y := by
    rcases hp with ht | hr
    · obtain ⟨a, b, hN, hb⟩ := shTop_nest m ht
      have hap : a 0 < b 0 := lv_xT hN
      have hpW : b 0 < shTw := hb ▸ ht.1
      refine ⟨a, b, hN, ?_, hb ▸ hpy⟩
      rcases lt_trichotomy (a 0) x with h | h | h
      · exact absurd (le2_le1 h2) (shD_noCross hap (lv_x2 hN) hpW x h (hb ▸ hxp.le) y (hb ▸ hpy))
      · subst h
        exact absurd h2 (shD_oneRight hap (lv_x2 hN) hpW y (hb ▸ hpy))
      · exact h
    · obtain ⟨a, b, hN, hxa, hbp⟩ := ((shRes_iff m).1 hr).2.2 x hxp
      exact ⟨a, b, hN, hxa, hbp.trans hpy⟩
  obtain ⟨a, b, hN, hxa, hby⟩ := hin
  exact ⟨consS x a, consS y b, hN.cons (fun _ => ⟨hxa, hby⟩) hxy h2, rfl, rfl⟩

end Seq

/-! ## `Y_{k+1} ⊆ Res_k` -/

/-- `k`-nests are cofinal below `u` if `u ≤₁ T` and a `k`-nest lies in `[u, T)`. -/
theorem shCof_le1 {k : ℕ} (hk : 1 ≤ k) {a b : ℕ → Ordinal.{0}} (hN : NestSeq k a b)
    {u T : Ordinal.{0}} (hu : le1 u T) (hua : u ≤ a 0) (hbT : b 0 < T) : shNestCof k u := by
  classical
  intro c hc
  set Z := nestPts k a b with hZdef
  have hZin : ∀ y ∈ Z, u ≤ y ∧ y < T := fun y hy =>
    ⟨hua.trans (hN.bounds hy).1, lt_of_le_of_lt (hN.bounds hy).2 hbT⟩
  obtain ⟨Yt, hy1, -, -, f, hf, -, hmap⟩ := le1_cof hu hc ∅ Z (by simp) hZin
    (by simpa using hN.closed)
  have hsub : (↑Z : Set Ordinal.{0}) = ↑(∅ ∪ Z) := by simp
  have hfN := hN.map (hsub ▸ hf.1.2.1) (fun x hx y hy hxy => hf.2.2 x (hsub ▸ hx) y (hsub ▸ hy) hxy)
  exact ⟨_, _, hfN, (hy1 _ (hmap _ (hN.a_mem (by omega)))).1,
    (hy1 _ (hmap _ (hN.b_mem (by omega)))).2⟩

/-- `k`-nests are cofinal below `w` if `u <₂ w`, `u ≤₁ T` and a `k`-nest lies in `[u, T)` ([C09]
Def 5.3 clause 2 of `u ≤₂ w`). -/
theorem shCof_le2 {k : ℕ} (hk : 1 ≤ k) {a b : ℕ → Ordinal.{0}} (hN : NestSeq k a b)
    {u T w : Ordinal.{0}} (hu : le1 u T) (hua : u ≤ a 0) (hbT : b 0 < T) (h2 : le2 u w) :
    shNestCof k w := by
  classical
  set Z := nestPts k a b with hZdef
  have hZ : Closed (↑Z : Set Ordinal.{0}) := hN.closed
  have hZin : ∀ y ∈ Z, u ≤ y ∧ y < T := fun y hy =>
    ⟨hua.trans (hN.bounds hy).1, lt_of_le_of_lt (hN.bounds hy).2 hbT⟩
  have hcof : CofCov R2C ∅ Z R2C u := by
    intro c' hc'
    obtain ⟨Yt, hy1, -, h3, f, hf, -, -⟩ := le1_cof hu hc' ∅ Z (by simp) hZin
      (by simpa using hZ)
    exact ⟨Yt, hy1, h3, f, by simpa using hf⟩
  obtain ⟨_, -, H2⟩ := le2_iff.1 h2
  have hcw := H2 ∅ (by simp) Z R2C hZ hcof
  intro c hc
  obtain ⟨Y, hY, -, g, hg⟩ := hcw c hc
  have hgN : NestSeq k (fun i => g (a i)) (fun i => g (b i)) :=
    hN.map hg.1.2.1 (fun x hx y hy hxy => hg.2.2 x hx y hy hxy)
  have hmap : ∀ z ∈ Z, g z ∈ Y := by
    intro z hz
    have := hg.1.1.mapsTo (Finset.mem_coe.2 hz)
    simpa using this
  exact ⟨_, _, hgN, (hY _ (hmap _ (hN.a_mem (by omega)))).1,
    (hY _ (hmap _ (hN.b_mem (by omega)))).2⟩

section Sub

variable (m : ℕ)

/-- A member `u ≤ a 0` of the block of a `(k+1)`-nest has `k`-nests cofinal below it. -/
theorem shCof_mem {a b : ℕ → Ordinal.{0}} (hN : NestSeq (m + 1 + 1) a b) {u : Ordinal.{0}}
    (hua : u ≤ a 0) (hu : le1 u (b 0)) : shNestCof (m + 1) u :=
  shCof_le1 (by omega) hN.tail hu (hua.trans (hN.1 0 (by omega)).1.le) (hN.1 0 (by omega)).2

/-- The top of a `(k+1)`-nest has `k`-nests cofinal below it. -/
theorem shCof_top {a b : ℕ → Ordinal.{0}} (hN : NestSeq (m + 1 + 1) a b) :
    shNestCof (m + 1) (b 0) :=
  shCof_le2 (by omega) hN.tail (le2_le1 (lv_x2 hN)) (hN.1 0 (by omega)).1.le
    (hN.1 0 (by omega)).2 (lv_x2 hN)

/-- **The level-`(k+1)` tops lie in `Res_k`.** -/
theorem shTop_sub_res {t : Ordinal.{0}} (ht : shTop (m + 1 + 1) t) : shRes (m + 1) t := by
  obtain ⟨a, b, hN, rfl⟩ := shTop_nest (m + 1) ht
  exact (shRes_iff m).2 ⟨ht.1, lt_of_le_of_lt zero_le (lv_xT hN), shCof_top m hN⟩

/-- **The level-`(k+1)` restarts lie in `Res_k`.** -/
theorem shRes_sub_res {p : Ordinal.{0}} (hp : shRes (m + 1 + 1) p) : shRes (m + 1) p := by
  obtain ⟨hpW, hp0, hcof⟩ := (shRes_iff (m + 1)).1 hp
  refine (shRes_iff m).2 ⟨hpW, hp0, fun c hc => ?_⟩
  obtain ⟨a, b, hN, hca, hbp⟩ := hcof c hc
  exact ⟨_, _, hN.tail, hca.trans (hN.1 0 (by omega)).1, (hN.1 0 (by omega)).2.trans hbp⟩

/-- **The left ends of pairs of depth `k + 1` (below `T_ω`) lie in `Res_k`.** -/
theorem shLeft_sub_res {a b : ℕ → Ordinal.{0}} (hN : NestSeq (m + 1 + 1) a b) (hW : b 0 < shTw) :
    shRes (m + 1) (a 0) :=
  (shRes_iff m).2 ⟨(lv_xT hN).trans hW, pos_iff_ne_zero.2 (hN.indec (hN.a_mem (by omega))).ne_zero,
    shCof_mem m hN le_rfl (le2_le1 (lv_x2 hN))⟩

/-- **Every `U_{k+1}(ξ)` (`ξ < T_ω`) lies in `Res_k`.** -/
theorem shU_sub_res {ξ u : Ordinal.{0}} (hξ : ξ < shTw) (hξu : ξ < u)
    (hu : u ≤ TkA ξ (m + 1 + 1)) (hu1 : le1 u (TkA ξ (m + 1 + 1))) : shRes (m + 1) u := by
  have hTW := shTkA_lt_Tw hξ (m + 1)
  obtain ⟨a, b, hN, hξa, hT⟩ := TkA_attained (hTW.trans shTw_lt_Om1)
  rw [← hT] at hu hu1 hTW
  have hcof : shNestCof (m + 1) u := by
    rcases le_or_gt u (a 0) with h | h
    · exact shCof_mem m hN h hu1
    · rcases eq_or_lt_of_le hu with he | he
      · rw [he]; exact shCof_top m hN
      · exact absurd hu1 (gap_emptyA hN hξa hT h he)
  exact (shRes_iff m).2 ⟨lt_of_le_of_lt hu hTW, lt_of_le_of_lt zero_le hξu, hcof⟩

/-- **`Y_{k+1} ⊆ Res_k`.** -/
theorem shY_sub_res {u : Ordinal.{0}} (hu : shY (m + 1 + 1) u) : shRes (m + 1) u := by
  rcases hu with h | ⟨ξ, hξ, hξu, hu, hu1⟩
  · exact shRes_sub_res m h
  · exact shU_sub_res m hξ hξu hu hu1

/-- **`Res_k ⊆ Y_k`.** -/
theorem shRes_sub_Y (k : ℕ) {u : Ordinal.{0}} (hu : shRes k u) : shY k u := Or.inl hu

end Sub

end Googology.Trans.PoR.InaccPsi.R2
