import Googology.Trans.BMS.PoR.PSS.Main.Iso
import Googology.Trans.BMS.PoR.PSS.Main.AF
import Googology.Trans.BMS.PoR.PSS.Main.BarEps
import Googology.Trans.BMS.PoR.PSS.Main.Fin

/-!
# `V_M` is finite: Theorem VF (`proof/PROOF-4.md` §15.1)

A set `F` of ordinals is **good** (`Good`) if it contains `0` and `1`, is closed
under additive decomposition, under `lh` on `(1, T¹ ∩ Ω_1)`, and under bar on the
additive principal elements of `(1, T¹ ∩ Ω_1)`.  `P_1(α)` is good (`good_P1`),
and it is the least good set containing `α`.

* **Lemma AF** (`lemmaAF`): if `F` is good, `N` is a standard root with at least
  two children and `o(N) ∈ F`, then `o(anchor N) ∈ F`.
* **Theorem VF** (`thmVF`): `o[V_M] ⊆ P_1(o(M))` for `o(M) ≥ 2`; so `V_M` is
  finite (`finite_V`), since `P_1(o(M))` is (Theorem FIN, `finite_P1` in `Main/Fin.lean`,
  proved without [CW12] Cor 6.3).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order Phi Forest

/-- **Lemma AF** (`proof/PROOF-4.md` §15.1): the anchor stays in a good set.  For
epsilon `N` this is `Bar_T` (`barEps`): `bar(o(N)) = o(anchor N)`; for non-epsilon `N`
it is `lemmaAF_noneps` (Fact BAR and Lemmas G, H). -/
theorem lemmaAF {F : Set Ordinal.{0}} (hF : Good F) {N a : Tm} (hN : Std N)
    (ha : anchor N = some a) (hNF : ordOf [N] ∈ F) : ordOf [a] ∈ F := by
  cases he : isEps N with
  | false => exact lemmaAF_noneps hF hN he ha hNF
  | true =>
    have hcs : N.cs ≠ [] := by
      intro h; rw [std_node_y hN, h] at ha; simp [anchor] at ha
    rw [← (barEps hN he).1 a ha]
    exact hF.bar_root hN hcs hNF

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
  have hsub : ordOf '' {x | InV M x} ⊆ {β | InP1 (ordOf M) β} := by
    rintro _ ⟨x, hx, rfl⟩
    exact thmVF hM hx
  exact Set.Finite.of_finite_image ((finite_P1 h1 (ordOf_lt_T1bound hM)).subset hsub)
    (fun x hx y hy e => ordOf_inj (stdOrd_of_inV hM hx) (stdOrd_of_inV hM hy) e)

end Googology.Trans.PSS.Main
