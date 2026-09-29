import Googology.Trans.PSS.Main.Iso

/-!
# `V_M` is finite: Theorem VF (`proof/PROOF-4.md` §15.1)

A set `F` of ordinals is **good** (`Good`) if it contains `0` and `1`, is closed
under additive decomposition, under `lh` on `(1, T¹ ∩ Ω_1)`, and under bar on the
additive principal elements of `(1, T¹ ∩ Ω_1)`.  `P_1(α)` is good (`good_P1`),
and it is the least good set containing `α`.

* **Lemma AF** (`lemmaAF`): if `F` is good, `N` is a standard root with at least
  two children and `o(N) ∈ F`, then `o(anchor N) ∈ F`.
* **Theorem VF** (`thmVF`): `o[V_M] ⊆ P_1(o(M))` for `o(M) ≥ 2`; so `V_M` is
  finite (`finite_V`), since `P_1(o(M))` is ([CW12] Cor 6.3 (1)).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order Phi Forest

/-- **Good sets** (`proof/PROOF-4.md` §15.1). -/
def Good (F : Set Ordinal.{0}) : Prop :=
  0 ∈ F ∧ 1 ∈ F ∧ (∀ l, ANF l → l.sum ∈ F → (∀ x ∈ l, x ∈ F) ∧ ∀ i, (l.take i).sum ∈ F) ∧
    (∀ β ∈ F, 1 < β → β < T1bound → ∀ δ, IsLh β δ → δ ∈ F) ∧
    (∀ β ∈ F, Pr β → 1 < β → β < T1bound → barO β ∈ F)

theorem good_P1 (α : Ordinal.{0}) : Good {β | InP1 α β} :=
  ⟨InP1.zero, InP1.one, fun _ hl hs => ⟨InP1.comp hl hs, InP1.psum hl hs⟩,
    fun _ hβ h1 hT _ hδ => InP1.lh hβ h1 hT hδ, fun _ hβ hP h1 hT => InP1.bar hβ hP h1 hT⟩

/-- **Lemma AF** (`proof/PROOF-4.md` §15.1): the anchor stays in a good set.  The
paper's proof uses Fact BAR ([CW12] Def 5.1, Lemmas 5.4, 5.10; [W07a] Lemmas 4.3,
4.9), Lemma R, `Bar_T` with Lemma TR, and Lemmas G and H. -/
theorem lemmaAF {F : Set Ordinal.{0}} (hF : Good F) {N a : Tm} (hN : Std N)
    (ha : anchor N = some a) (hNF : ordOf [N] ∈ F) : ordOf [a] ∈ F := by
  sorry

theorem ordOf_leaf_eq : ordOf [Tm.node 0 []] = 1 := TR.ordOf_leaf

/-- `o` of the prefix of a node is a partial sum of the additive normal form. -/
theorem ordOf_take {x : List Tm} (hx : StdOrd x) (i : ℕ) :
    ordOf (x.take i) = ((anfOf x).take i).sum := by
  rw [take_anfOf, sum_anfOf (stdOrd_take hx i)]

/-- **Theorem VF** (`proof/PROOF-4.md` §15.1): `o[V_M] ⊆ P_1(o(M))`. -/
theorem thmVF {M : List Tm} (hM : StdOrd M) {x : List Tm} (hx : InV M x) :
    InP1 (ordOf M) (ordOf x) := by
  have hG := good_P1 (ordOf M)
  induction hx with
  | nil => rw [ordOf_nil]; exact InP1.zero
  | one => rw [ordOf_leaf_eq]; exact InP1.one
  | self => exact InP1.self
  | take hx i ih =>
    have hxs := stdOrd_of_inV hM hx
    rw [ordOf_take hxs]
    exact InP1.psum (anf_anfOf hxs) (by rw [sum_anfOf hxs]; exact ih) i
  | seg hx t ht ih =>
    have hxs := stdOrd_of_inV hM hx
    exact InP1.comp (anf_anfOf hxs) (by rw [sum_anfOf hxs]; exact ih) _
      (List.mem_map.mpr ⟨t, ht, rfl⟩)
  | anc ht ha ih =>
    have hts := stdOrd_of_inV hM ht
    exact lemmaAF hG (((stdOrd_iff _).mp hts).2 _ (by simp)) ha ih
  | lh ht ih =>
    rename_i t
    have hts := stdOrd_of_inV hM ht
    have htstd : Std t := ((stdOrd_iff _).mp hts).2 _ (by simp)
    have hL := lemmaL htstd
    rcases le_or_gt (ordOf [t]) 1 with h1 | h1
    · have hnl : ¬ InL (ordOf [t]) := by
        rcases h1.lt_or_eq with h0 | h0
        · rw [Order.lt_one_iff.mp h0]; exact not_inL_zero
        · rw [h0]; exact not_inL_one
      have := hL.unique (isLh_self_of_not_inL hnl)
      rw [this]; exact ih
    · exact InP1.lh ih h1 (ordOf_lt_T1bound hts) hL

/-- **`V_M` is finite.** -/
theorem finite_V {M : List Tm} (hM : StdOrd M) (h1 : 1 < ordOf M) : {x | InV M x}.Finite := by
  obtain ⟨X, hX, -⟩ := P1_isominimal h1 (ordOf_lt_T1bound hM)
  have hsub : ordOf '' {x | InV M x} ⊆ X := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hX]; exact thmVF hM hx
  exact Set.Finite.of_finite_image ((X.finite_toSet).subset hsub)
    (fun x hx y hy e => ordOf_inj (stdOrd_of_inV hM hx) (stdOrd_of_inV hM hy) e)

end Googology.Trans.PSS.Main
