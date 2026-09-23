/-
Ported verbatim from koteitan/trio, `lean/Lift.lean`:
https://github.com/koteitan/trio/blob/74ef7af49eefaef06ce4c9b57c02ecdcb9975606/lean/Lift.lean
Only the module names of the imports and the namespace (`TRIO` →
`Googology.Trans.BMS.TrioCof`) were changed. The bridge to this library's
Bashicu matrices is `Googology/Trans/BMS/TrioCofinal.lean`.
-/
/-
Lift.lean: 心材リフト（guarded lift）`lsub` の項理論。

ガード付きコピー（上昇行列 A_x1 が 0/1 混在）の translate は、bad part の
translate に `lsub w1 s` を施したものになる（w1 = バッドルートの行 1 値、
s = k·d1、経路補題により `le1` ガード = 木の経路上の行 1 窓条件）。
`lsub w1 s` は「根から第 1 添字が w1 を超える節だけを通って到達できる
心材（heartwood）」の第 1 添字に一様に s を加える。閾値以下の節では
引数部分木は手つかずのまま、兄弟末尾だけ走査を続ける。
-/
import Googology.Trans.BMS.TrioCof.Cnf

namespace Googology.Trans.BMS.TrioCof

open Three

namespace Three

/-- The guarded (heartwood) lift. -/
def lsub (w1 s : ℕ) : Three → Three
  | Z => Z
  | P a1 a2 b c =>
      if w1 < a1 then P (a1 + s) a2 (lsub w1 s b) (lsub w1 s c)
      else P a1 a2 b (lsub w1 s c)

@[simp] theorem lsub_Z (w1 s : ℕ) : lsub w1 s Z = Z := rfl

theorem lsub_P (w1 s a1 a2 : ℕ) (b c : Three) :
    lsub w1 s (P a1 a2 b c) =
      if w1 < a1 then P (a1 + s) a2 (lsub w1 s b) (lsub w1 s c)
      else P a1 a2 b (lsub w1 s c) := rfl

theorem lsub_P_pos {w1 a1 : ℕ} (h : w1 < a1) (s a2 : ℕ) (b c : Three) :
    lsub w1 s (P a1 a2 b c) = P (a1 + s) a2 (lsub w1 s b) (lsub w1 s c) := by
  rw [lsub_P, if_pos h]

theorem lsub_P_neg {w1 a1 : ℕ} (h : ¬ w1 < a1) (s a2 : ℕ) (b c : Three) :
    lsub w1 s (P a1 a2 b c) = P a1 a2 b (lsub w1 s c) := by
  rw [lsub_P, if_neg h]

/-- `s = 0` のリフトは恒等（`t ≤ 1` のステップの一様コピーを回収する）。 -/
theorem lsub_zero (w1 : ℕ) : ∀ t : Three, lsub w1 0 t = t
  | Z => rfl
  | P a1 a2 b c => by
    rw [lsub_P]
    split_ifs with h
    · rw [lsub_zero w1 b, lsub_zero w1 c, Nat.add_zero]
    · rw [lsub_zero w1 c]

/-! ### 全順序性 -/

theorem olt_total : ∀ x y : Three, x = y ∨ x <o y ∨ y <o x
  | Z, Z => Or.inl rfl
  | Z, P _ _ _ _ => Or.inr (Or.inl trivial)
  | P _ _ _ _, Z => Or.inr (Or.inr trivial)
  | P a1 a2 b c, P e1 e2 f g => by
    rcases Nat.lt_trichotomy a1 e1 with h1 | rfl | h1
    · exact Or.inr (Or.inl (Or.inl h1))
    · rcases Nat.lt_trichotomy a2 e2 with h2 | rfl | h2
      · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨rfl, h2⟩)))
      · rcases olt_total b f with rfl | h3 | h3
        · rcases olt_total c g with rfl | h4 | h4
          · exact Or.inl rfl
          · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, h4⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, h4⟩))))
        · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h3⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h3⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h2⟩)))
    · exact Or.inr (Or.inr (Or.inl h1))

theorem olt_asymm {x y : Three} (h : x <o y) : ¬ y <o x :=
  fun h' => olt_irrefl x (olt_trans h h')

theorem not_olt_iff_ole {x y : Three} : ¬ x <o y ↔ y ≤o x := by
  constructor
  · intro h
    rcases olt_total x y with rfl | h' | h'
    · exact Or.inr rfl
    · exact absurd h' h
    · exact Or.inl h'
  · rintro (h | rfl) h'
    · exact olt_asymm h h'
    · exact olt_irrefl _ h'

/-! ### リフトの単調性 -/

theorem olt_lsub (w1 s : ℕ) : ∀ (x y : Three), x <o y →
    lsub w1 s x <o lsub w1 s y
  | Z, Z, h => absurd h (olt_irrefl Z)
  | Z, P e1 e2 f g, _ => by
    rw [lsub_P]
    split_ifs <;> exact trivial
  | P _ _ _ _, Z, h => absurd h (not_olt_Z _)
  | P a1 a2 b c, P e1 e2 f g, h => by
    rcases (olt_P_P).1 h with h1 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h3⟩ | ⟨rfl, rfl, rfl, h4⟩
    · -- first subscripts strictly increase
      rw [lsub_P, lsub_P]
      split_ifs with ha he he <;> rw [olt_P_P]
      · exact Or.inl (by omega)
      · exact absurd h1 (by omega)
      · exact Or.inl (by omega)
      · exact Or.inl h1
    · -- equal first, second strictly increases
      rw [lsub_P, lsub_P]
      split_ifs with ha
      · exact Or.inr (Or.inl ⟨rfl, h2⟩)
      · exact Or.inr (Or.inl ⟨rfl, h2⟩)
    · -- equal pair, arguments compare
      rw [lsub_P, lsub_P]
      split_ifs with ha
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, olt_lsub w1 s b f h3⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h3⟩))
    · -- equal pair and argument, tails compare
      rw [lsub_P, lsub_P]
      split_ifs with ha
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, olt_lsub w1 s c g h4⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, olt_lsub w1 s c g h4⟩))

theorem ole_lsub (w1 s : ℕ) {x y : Three} (h : x ≤o y) :
    lsub w1 s x ≤o lsub w1 s y := by
  rcases h with h | rfl
  · exact Or.inl (olt_lsub w1 s x y h)
  · exact Or.inr rfl

end Three

/-! ### `cnf` の保存 -/

open Three

/-- 心材リフトは Cantor 標準形条件を保つ。 -/
theorem cnf_lsub (w1 s : ℕ) : ∀ (t : Three), cnf t → cnf (lsub w1 s t)
  | Z, _ => trivial
  | P a1 a2 b Z, h => by
    rw [lsub_P]
    split_ifs with ha
    · exact cnf_lsub w1 s b (cnf_P_Z.1 h)
    · exact h
  | P a1 a2 b (P e1 e2 f g), h => by
    obtain ⟨hb, hcut, hc⟩ := cnf_P_P.1 h
    rw [lsub_P, lsub_P]
    split_ifs with ha he he
    · -- both above the threshold: monotonicity transfers the cut comparison
      rw [cnf_P_P]
      refine ⟨cnf_lsub w1 s b hb, ?_, ?_⟩
      · have hle : P e1 e2 f Z ≤o P a1 a2 b Z := not_olt_iff_ole.1 hcut
        have := ole_lsub w1 s hle
        rw [lsub_P_pos he, lsub_P_pos ha, lsub_Z] at this
        exact not_olt_iff_ole.2 this
      · have := cnf_lsub w1 s (P e1 e2 f g) hc
        rwa [lsub_P_pos he] at this
    · -- left lifted, right at/below the threshold: heads strictly separate
      rw [cnf_P_P]
      refine ⟨cnf_lsub w1 s b hb, ?_, ?_⟩
      · intro hlt
        rcases (olt_P_P).1 hlt with h1 | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
      · have := cnf_lsub w1 s (P e1 e2 f g) hc
        rwa [lsub_P_neg he] at this
    · -- left at/below, right above: impossible by the pre-step cut condition
      exact absurd (Or.inl (by omega)) hcut
    · -- both at/below: the cut comparison is untouched
      rw [cnf_P_P]
      refine ⟨hb, hcut, ?_⟩
      have := cnf_lsub w1 s (P e1 e2 f g) hc
      rwa [lsub_P_neg he] at this

end Googology.Trans.BMS.TrioCof
