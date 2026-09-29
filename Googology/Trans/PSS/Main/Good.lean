import Googology.Trans.PSS.Main.Cited

/-!
# Good sets (`proof/PROOF-4.md` §15.1)

A set `F` of ordinals is **good** if it contains `0` and `1`, is closed under
additive decomposition, under `lh` on `(1, T¹ ∩ Ω_1)`, and under bar on the
additive principal elements of `(1, T¹ ∩ Ω_1)`.  `P_1(α)` is good (`good_P1`).
-/

namespace Googology.Trans.PSS.Main

/-- **Good sets** (`proof/PROOF-4.md` §15.1). -/
def Good (F : Set Ordinal.{0}) : Prop :=
  0 ∈ F ∧ 1 ∈ F ∧ (∀ l, ANF l → l.sum ∈ F → (∀ x ∈ l, x ∈ F) ∧ ∀ i, (l.take i).sum ∈ F) ∧
    (∀ β ∈ F, 1 < β → β < T1bound → ∀ δ, IsLh β δ → δ ∈ F) ∧
    (∀ β ∈ F, Pr β → 1 < β → β < T1bound → barO β ∈ F)

theorem good_P1 (α : Ordinal.{0}) : Good {β | InP1 α β} :=
  ⟨InP1.zero, InP1.one, fun _ hl hs => ⟨InP1.comp hl hs, InP1.psum hl hs⟩,
    fun _ hβ h1 hT _ hδ => InP1.lh hβ h1 hT hδ, fun _ hβ hP h1 hT => InP1.bar hβ hP h1 hT⟩

end Googology.Trans.PSS.Main
