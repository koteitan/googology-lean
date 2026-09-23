/-
Ported verbatim from koteitan/trio, `lean/Zjump.lean`:
https://github.com/koteitan/trio/blob/74ef7af49eefaef06ce4c9b57c02ecdcb9975606/lean/Zjump.lean
Only the module names of the imports and the namespace (`TRIO` →
`Googology.Trans.BMS.TrioCof`) were changed. The bridge to this library's
Bashicu matrices is `Googology/Trans/BMS/TrioCofinal.lean`.
-/
/-
Zjump.lean: `zjump` の展開保存。

パターン (p, q') の領域分割: A 取り部・B1 同一コピー・B2 コピー横断・
C 交差。ガード付きリフトの相互作用は経路遮断（le1_of_chain_le1）と
窓スパインで閉じる。probe: 5 不変量 + zjump は per-step 閉
（236277 展開 0 違反）。
-/
import Googology.Trans.BMS.TrioCof.Invariant

namespace Googology.Trans.BMS.TrioCof

open Classical

set_option maxHeartbeats 2000000 in
/-- **The z-jump prohibition survives the expansion.** -/
theorem zjump_oper {M : TrioSeq} {n : ℕ} (hn : 1 ≤ n) (hr : r1ok M)
    (hz2 : z2ok M) (hmp : markP1 M) (h : zjump M) : zjump (M⟦n⟧) := by
  by_cases hL : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]
    exact h
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL hz]
    unfold Pred
    split_ifs
    · exact h
    · exact zjump_dropLast h
  by_cases hp : hasParent M (srow M (M.length - 1)) (M.length - 1)
  case neg =>
    rw [oper_eq_pred_of_noParent n hL hz hp]
    unfold Pred
    split_ifs
    · exact h
    · exact zjump_dropLast h
  case pos =>
    have np := parent_nextR hp
    have j0lt : parent M (srow M (M.length - 1)) (M.length - 1)
        < M.length - 1 := nextR_index_lt np
    have chain := nextR_chain0 np
    have iv : ∀ k, parent M (srow M (M.length - 1)) (M.length - 1) < k →
        k ≤ M.length - 1 →
        entry M 0 (parent M (srow M (M.length - 1)) (M.length - 1))
          < entry M 0 k :=
      fun k h1 h2 => le0_interval_gt chain k ⟨h1, h2⟩
    set j0 := parent M (srow M (M.length - 1)) (M.length - 1) with hj0
    set L := M.length - 1 - j0 with hLdef
    set d0i := (if 0 < srow M (M.length - 1)
      then entry M 0 (M.length - 1) - entry M 0 j0 else 0) with hd0i
    set d1i := (if 1 < srow M (M.length - 1)
      then entry M 1 (M.length - 1) - entry M 1 j0 else 0) with hd1i
    have hLpos : 0 < L := by omega
    have hj0b : j0 < M.length := by omega
    have htklen : (M.take j0).length = j0 := by
      rw [List.length_take]
      omega
    rw [oper_gcopies n hL hz hp, ← hj0, ← hLdef, ← hd0i, ← hd1i]
    set X := M.take j0 ++ gcopies M j0 L d0i d1i n with hX
    have hXlen : X.length = j0 + n * L := by
      rw [hX, List.length_append, htklen, gcopies_length]
    have egG : ∀ x, x < j0 → X.getD x (0, 0, 0) = M.getD x (0, 0, 0) := by
      intro x hx
      rw [hX, getD_append_left (by rw [htklen]; exact hx), getD_take hx]
    have egC : ∀ k' q', k' < n → q' < L →
        X.getD (j0 + (k' * L + q')) (0, 0, 0)
          = (entry M 0 (j0 + q') + k' * d0i,
             entry M 1 (j0 + q')
               + (if le1 M j0 (j0 + q') then k' * d1i else 0),
             entry M 2 (j0 + q')) := by
      intro k' q' hk' hq'
      rw [hX, getD_app_right _ _ (by rw [htklen]; omega), htklen,
        show j0 + (k' * L + q') - j0 = k' * L + q' from by omega,
        gcopies_getD hk' hq']
    intro pi pj hpij hpjb hsub heq hsp
    rw [hXlen] at hpjb
    by_cases hjG : pj < j0
    · have he : ∀ x, x ≤ pj → ∀ r', entry X r' x = entry M r' x := by
        intro x hx r'
        unfold entry
        rw [egG x (by omega)]
      show entry X 2 pj ≤ entry X 2 pi
      rw [he pj le_rfl 2, he pi (by omega) 2]
      refine h pi pj hpij (by omega) ?_ ?_ ?_
      · intro l h1 h2
        have := hsub l h1 h2
        rwa [he pi (by omega) 0, he l (by omega) 0] at this
      · have := heq
        rwa [he pj le_rfl 1, he pi (by omega) 1] at this
      · intro l h1 h2 h3 h4
        have := hsp l h1 h2 (by rwa [he l (by omega) 0, he pj le_rfl 0]) (by
          intro l' hl1 hl2
          have := h4 l' hl1 hl2
          rwa [← he l (by omega) 0, ← he l' (by omega) 0] at this)
        rwa [he pi (by omega) 1, he l (by omega) 1] at this
    · push Not at hjG
      obtain ⟨kq, qq, hkqn, hqqL, hpe⟩ :=
        index_decomp hLpos (show pj - j0 < n * L by omega)
      have hpjeq : pj = j0 + (kq * L + qq) := by omega
      by_cases hiG : pi < j0
      · -- region C: the source in the take part
        -- goal in mixed terms; trivial unless the target is marked
        rw [hpjeq]
        show entry X 2 (j0 + (kq * L + qq)) ≤ entry X 2 pi
        unfold entry
        rw [egC kq qq hkqn hqqL, egG pi hiG]
        show entry M 2 (j0 + qq) ≤ (M.getD pi (0, 0, 0)).2.2
        by_cases hmk : entry M 2 (j0 + qq) = 0
        · omega
        have hmk1 : (M.getD (j0 + qq) (0, 0, 0)).2.2 = 1 := by
          have := hz2 (j0 + qq) (by omega)
          have e2 : entry M 2 (j0 + qq) = (M.getD (j0 + qq) (0, 0, 0)).2.2 := rfl
          omega
        -- the row-1 equality in mixed terms
        have heqH : entry M 1 (j0 + qq)
              + (if le1 M j0 (j0 + qq) then kq * d1i else 0)
            = (M.getD pi (0, 0, 0)).2.1 := by
          have := heq
          rw [hpjeq] at this
          unfold entry at this
          rw [egC kq qq hkqn hqqL, egG pi hiG] at this
          exact this
        -- the subtree condition puts `pi` strictly below the base level
        have hpiv : (M.getD pi (0, 0, 0)).1 < entry M 0 j0 := by
          have := hsub (j0 + (0 * L + 0)) (by
            have hz0L : 0 * L = 0 := Nat.zero_mul L
            omega) (by
            rw [hpjeq]
            have hz0L : 0 * L = 0 := Nat.zero_mul L
            omega)
          unfold entry at this
          rw [egC 0 0 (by omega) (by omega), egG pi hiG] at this
          have this' : (M.getD pi (0, 0, 0)).1
              < entry M 0 (j0 + 0) + 0 * d0i := this
          simp only [Nat.add_zero, Nat.zero_mul] at this'
          exact this'
        -- the spine transfer for host windows ending at block columns
        have hspT : ∀ jt, j0 ≤ jt → jt < j0 + L →
            (∀ l'', jt < l'' → l'' < j0 + qq →
              entry M 0 jt < entry M 0 l'') →
            entry M 0 jt < entry M 0 (j0 + qq) →
            jt ≤ j0 + qq →
            (M.getD pi (0, 0, 0)).2.1
              ≤ entry M 1 jt + (if le1 M j0 jt then kq * d1i else 0) := by
          intro jt hjt1 hjt2 hwin hlt hle
          rcases Nat.eq_or_lt_of_le hle with rfl | hltq
          · exfalso
            omega
          have := hsp (j0 + (kq * L + (jt - j0))) (by omega) (by
              rw [hpjeq]
              omega) (by
              rw [hpjeq]
              unfold entry
              rw [egC kq (jt - j0) hkqn (by omega), egC kq qq hkqn hqqL]
              show entry M 0 (j0 + (jt - j0)) + kq * d0i
                < entry M 0 (j0 + qq) + kq * d0i
              rw [show j0 + (jt - j0) = jt from by omega]
              omega) (by
              intro l'' hl1 hl2
              rw [hpjeq] at hl2
              have hlq : ∃ q'', jt - j0 < q'' ∧ q'' < qq
                  ∧ l'' = j0 + (kq * L + q'') :=
                ⟨l'' - j0 - kq * L, by omega, by omega, by omega⟩
              obtain ⟨q'', hq1, hq2, rfl⟩ := hlq
              unfold entry
              rw [egC kq (jt - j0) hkqn (by omega), egC kq q'' hkqn (by omega)]
              show entry M 0 (j0 + (jt - j0)) + kq * d0i
                < entry M 0 (j0 + q'') + kq * d0i
              have := hwin (j0 + q'') (by omega) (by omega)
              rw [show j0 + (jt - j0) = jt from by omega]
              omega)
          unfold entry at this
          rw [egC kq (jt - j0) hkqn (by omega), egG pi hiG] at this
          rw [show j0 + (jt - j0) = jt from by omega] at this
          exact this
        by_cases hd1z : d1i = 0
        · -- `t = 1`: host instance from the take-part source
          have hze : ∀ (c : Prop) [Decidable c] (k'' : ℕ),
              (if c then k'' * d1i else 0) = 0 := by
            intro c _ k''
            rw [hd1z, Nat.mul_zero]
            exact ite_self 0
          rw [hze] at heqH
          refine h pi (j0 + qq) (by omega) (by omega) ?_ (by
            have e1 : entry M 1 (j0 + qq)
              = (M.getD (j0 + qq) (0, 0, 0)).2.1 := rfl
            have e1' : entry M 1 pi = (M.getD pi (0, 0, 0)).2.1 := rfl
            show entry M 1 (j0 + qq) = entry M 1 pi
            omega) ?_
          · -- subtree: take part by the X condition, block part by `iv`
            intro l h1 h2
            rcases Nat.lt_or_ge l j0 with hlG | hlG
            · have := hsub l h1 (by
                rw [hpjeq]
                omega)
              unfold entry at this
              rw [egG pi hiG, egG l hlG] at this
              exact this
            · show entry M 0 pi < entry M 0 l
              have e0 : entry M 0 pi = (M.getD pi (0, 0, 0)).1 := rfl
              rcases Nat.eq_or_lt_of_le hlG with rfl | hlG'
              · omega
              · have := iv l (by omega) (by omega)
                omega
          · -- spine
            intro l h1 h2 h3 h4
            rcases Nat.lt_or_ge l j0 with hlG | hlG
            · -- take-part visible: below the base, so X-visible
              have hlv : entry M 0 l < entry M 0 j0 := by
                rcases Nat.eq_zero_or_pos qq with rfl | hqqpos
                · have e := h3
                  rw [Nat.add_zero] at e
                  exact e
                · by_contra hcon
                  push Not at hcon
                  have := h4 j0 (by omega) (by omega)
                  have := iv (j0 + qq) (by omega) (by omega)
                  omega
              have := hsp l h1 (by
                  rw [hpjeq]
                  omega) (by
                  rw [hpjeq]
                  unfold entry
                  rw [egG l hlG, egC kq qq hkqn hqqL]
                  show entry M 0 l < entry M 0 (j0 + qq) + kq * d0i
                  omega) (by
                  intro l'' hl1 hl2
                  rw [hpjeq] at hl2
                  rcases Nat.lt_or_ge l'' j0 with hl''G | hl''G
                  · unfold entry
                    rw [egG l hlG, egG l'' hl''G]
                    exact h4 l'' hl1 (by omega)
                  · obtain ⟨k'', q'', hk''n, hq''L, hle''⟩ :=
                      index_decomp hLpos (show l'' - j0 < n * L by omega)
                    have hleq : l'' = j0 + (k'' * L + q'') := by omega
                    rw [hleq]
                    unfold entry
                    rw [egG l hlG, egC k'' q'' hk''n hq''L]
                    show entry M 0 l < entry M 0 (j0 + q'') + k'' * d0i
                    have hbase : entry M 0 j0 ≤ entry M 0 (j0 + q'') := by
                      rcases Nat.eq_zero_or_pos q'' with rfl | hq''pos
                      · rw [Nat.add_zero]
                      · exact (iv (j0 + q'') (by omega) (by omega)).le
                    omega)
              unfold entry at this
              rw [egG pi hiG, egG l hlG] at this
              show entry M 1 pi ≤ entry M 1 l
              have e1 : entry M 1 pi = (M.getD pi (0, 0, 0)).2.1 := rfl
              have e1' : entry M 1 l = (M.getD l (0, 0, 0)).2.1 := rfl
              exact this
            · -- block-part visible: through the copy image
              have := hspT l hlG (by omega) (fun l'' a b => h4 l'' a b) h3 (by omega)
              rw [hze] at this
              show entry M 1 pi ≤ entry M 1 l
              have e1' : entry M 1 pi = (M.getD pi (0, 0, 0)).2.1 := rfl
              omega
        · -- `t = 2`: analysis by the guard of the marked target
          have hd1pos : 0 < d1i := by omega
          have hi2 : 1 < srow M (M.length - 1) := by
            by_contra hcon
            push Not at hcon
            rw [hd1i, if_neg (by omega)] at hd1pos
            omega
          have np2 : nextrel2 M j0 (M.length - 1) := by
            have np' := np
            unfold nextR at np'
            rw [if_neg (by omega : ¬ srow M (M.length - 1) = 0),
              if_neg (by omega : ¬ srow M (M.length - 1) = 1)] at np'
            exact np'
          have hj00 : entry M 2 j0 = 0 := by
            have h2lt := np2.2.2.2.1
            have := hz2 (M.length - 1) (by omega)
            have e2a : entry M 2 j0 = (M.getD j0 (0, 0, 0)).2.2 := rfl
            have e2b : entry M 2 (M.length - 1)
              = (M.getD (M.length - 1) (0, 0, 0)).2.2 := rfl
            omega
          have hqqpos : 0 < qq := by
            by_contra hq0
            push Not at hq0
            have he : qq = 0 := by omega
            subst he
            rw [Nat.add_zero] at hmk
            exact hmk hj00
          have hRq' : (M.getD pi (0, 0, 0)).2.1
              ≤ entry M 1 j0 + kq * d1i := by
            have := hspT j0 le_rfl (by omega)
              (fun l'' h1 h2 => iv l'' (by omega) (by omega))
              (iv (j0 + qq) (by omega) (by omega)) (by omega)
            rw [if_pos (le1_refl hj0b)] at this
            exact this
          by_cases hDq : le1 M j0 (j0 + qq)
          · exfalso
            rw [if_pos hDq] at heqH
            have hgt := rtg1_entry1_lt hDq.2.2 (by omega)
            omega
          · rw [if_neg hDq] at heqH
            rw [Nat.add_zero] at heqH
            -- the marked target's row 1 cannot exceed the base (else blocker)
            have hle' : entry M 1 (j0 + qq) ≤ entry M 1 j0 := by
              by_contra hgt'
              push Not at hgt'
              obtain ⟨b, hb1, hb2, hb3, hb4⟩ :=
                blocker_of_not_le1 (le0_interval_desc chain (by omega)
                  (j0 + qq) (by omega) (by omega)) (by omega) hDq
              rcases Nat.eq_or_lt_of_le (nextrel0_rtrancl_index_le hb2)
                  with rfl | hbq
              · omega
              · have hbj0 : j0 < b := by
                  have := nextrel0_rtrancl_index_le hb1
                  rcases Nat.eq_or_lt_of_le this with rfl | h'
                  · exact absurd rfl hb3
                  · exact h'
                have hbD : ¬ le1 M j0 b := by
                  intro hle
                  have := rtg1_entry1_lt hle.2.2 (by omega)
                  omega
                have := hspT b (by omega) (by
                    have := nextrel0_rtrancl_index_le hb2
                    omega) (by
                    intro l'' hl1 hl2
                    exact le0_interval_gt hb2 l'' ⟨hl1, by omega⟩) (by
                    exact le0_interval_gt hb2 (j0 + qq) ⟨by omega, le_rfl⟩)
                  (by omega)
                rw [if_neg hbD] at this
                omega
            -- host instance from the take-part source to the target
            refine h pi (j0 + qq) (by omega) (by omega) ?_ (by
              have e1 : entry M 1 (j0 + qq)
                = (M.getD (j0 + qq) (0, 0, 0)).2.1 := rfl
              have e1' : entry M 1 pi = (M.getD pi (0, 0, 0)).2.1 := rfl
              show entry M 1 (j0 + qq) = entry M 1 pi
              omega) ?_
            · intro l h1 h2
              rcases Nat.lt_or_ge l j0 with hlG | hlG
              · have := hsub l h1 (by
                  rw [hpjeq]
                  omega)
                unfold entry at this
                rw [egG pi hiG, egG l hlG] at this
                exact this
              · show entry M 0 pi < entry M 0 l
                have e0 : entry M 0 pi = (M.getD pi (0, 0, 0)).1 := rfl
                rcases Nat.eq_or_lt_of_le hlG with rfl | hlG'
                · omega
                · have := iv l (by omega) (by omega)
                  omega
            · intro l h1 h2 h3 h4
              rcases Nat.lt_or_ge l j0 with hlG | hlG
              · have hlv : entry M 0 l < entry M 0 j0 := by
                  by_contra hcon
                  push Not at hcon
                  have := h4 j0 (by omega) (by omega)
                  have := iv (j0 + qq) (by omega) (by omega)
                  omega
                have := hsp l h1 (by
                    rw [hpjeq]
                    omega) (by
                    rw [hpjeq]
                    unfold entry
                    rw [egG l hlG, egC kq qq hkqn hqqL]
                    show entry M 0 l < entry M 0 (j0 + qq) + kq * d0i
                    omega) (by
                    intro l'' hl1 hl2
                    rw [hpjeq] at hl2
                    rcases Nat.lt_or_ge l'' j0 with hl''G | hl''G
                    · unfold entry
                      rw [egG l hlG, egG l'' hl''G]
                      exact h4 l'' hl1 (by omega)
                    · obtain ⟨k'', q'', hk''n, hq''L, hle''⟩ :=
                        index_decomp hLpos (show l'' - j0 < n * L by omega)
                      have hleq : l'' = j0 + (k'' * L + q'') := by omega
                      rw [hleq]
                      unfold entry
                      rw [egG l hlG, egC k'' q'' hk''n hq''L]
                      show entry M 0 l < entry M 0 (j0 + q'') + k'' * d0i
                      have hbase : entry M 0 j0 ≤ entry M 0 (j0 + q'') := by
                        rcases Nat.eq_zero_or_pos q'' with rfl | hq''pos
                        · rw [Nat.add_zero]
                        · exact (iv (j0 + q'') (by omega) (by omega)).le
                      omega)
                unfold entry at this
                rw [egG pi hiG, egG l hlG] at this
                show entry M 1 pi ≤ entry M 1 l
                exact this
              · have := hspT l hlG (by omega) (fun l'' a b => h4 l'' a b) h3
                  (by omega)
                show entry M 1 pi ≤ entry M 1 l
                have e1' : entry M 1 pi = (M.getD pi (0, 0, 0)).2.1 := rfl
                by_cases hDl : le1 M j0 l
                · rcases Nat.eq_or_lt_of_le hlG with rfl | hlj0'
                  · omega
                  · rw [if_pos hDl] at this
                    have := rtg1_entry1_lt hDl.2.2 (by omega)
                    omega
                · rw [if_neg hDl] at this
                  omega
      · push Not at hiG
        obtain ⟨kp, qp, hkpn, hqpL, hpe'⟩ :=
          index_decomp hLpos (show pi - j0 < n * L by omega)
        have hpieq : pi = j0 + (kp * L + qp) := by omega
        have hkpq : kp ≤ kq := by
          by_contra hcon
          push Not at hcon
          have hm : (kq + 1) * L ≤ kp * L := Nat.mul_le_mul_right L (by omega)
          have hs : (kq + 1) * L = kq * L + L := Nat.succ_mul kq L
          omega
        rcases Nat.eq_or_lt_of_le hkpq with rfl | hklt
        · -- B1: same copy
          have hqpq : qp < qq := by omega
          have hsubH : ∀ l, j0 + qp < l → l ≤ j0 + qq →
              entry M 0 (j0 + qp) < entry M 0 l := by
            intro l h1 h2
            have := hsub (j0 + (kp * L + (l - j0))) (by
              rw [hpieq]
              omega) (by
              rw [hpjeq]
              omega)
            rw [hpieq] at this
            unfold entry at this
            rw [egC kp qp hkpn hqpL, egC kp (l - j0) hkpn (by omega)] at this
            rw [show j0 + (l - j0) = l from by omega] at this
            have this' : entry M 0 (j0 + qp) + kp * d0i
                < entry M 0 l + kp * d0i := this
            show entry M 0 (j0 + qp) < entry M 0 l
            omega
          have hrtgpq : Relation.ReflTransGen (nextrel0 M) (j0 + qp) (j0 + qq) := by
            refine rtg0_of_window (by omega) (by omega) ?_
            intro l h1 h2
            exact hsubH l h1 h2
          have hrtgj0q : Relation.ReflTransGen (nextrel0 M) j0 (j0 + qq) :=
            le0_interval_desc chain (by omega) (j0 + qq) (by omega) (by omega)
          have hrtgj0p : Relation.ReflTransGen (nextrel0 M) j0 (j0 + qp) :=
            rtg0_comparable hrtgj0q hrtgpq (by omega)
          have heqH : entry M 1 (j0 + qq)
                + (if le1 M j0 (j0 + qq) then kp * d1i else 0)
              = entry M 1 (j0 + qp)
                + (if le1 M j0 (j0 + qp) then kp * d1i else 0) := by
            have := heq
            rw [hpieq, hpjeq] at this
            unfold entry at this
            rw [egC kp qp hkpn hqpL, egC kp qq hkpn hqqL] at this
            exact this
          have hspH : ∀ l, j0 + qp < l → l < j0 + qq →
              entry M 0 l < entry M 0 (j0 + qq) →
              (∀ l', l < l' → l' < j0 + qq → entry M 0 l < entry M 0 l') →
              entry M 1 (j0 + qp)
                  + (if le1 M j0 (j0 + qp) then kp * d1i else 0)
                ≤ entry M 1 l + (if le1 M j0 l then kp * d1i else 0) := by
            intro l h1 h2 h3 h4
            have := hsp (j0 + (kp * L + (l - j0))) (by
                rw [hpieq]
                omega) (by
                rw [hpjeq]
                omega)
              (by
                rw [hpjeq]
                unfold entry
                rw [egC kp (l - j0) hkpn (by omega), egC kp qq hkpn hqqL]
                show entry M 0 (j0 + (l - j0)) + kp * d0i
                  < entry M 0 (j0 + qq) + kp * d0i
                rw [show j0 + (l - j0) = l from by omega]
                omega)
              (by
                intro l'' hl1 hl2
                rw [hpjeq] at hl2
                have hlq : ∃ q'', l - j0 < q'' ∧ q'' < qq
                    ∧ l'' = j0 + (kp * L + q'') :=
                  ⟨l'' - j0 - kp * L, by omega, by omega, by omega⟩
                obtain ⟨q'', hq1, hq2, rfl⟩ := hlq
                unfold entry
                rw [egC kp (l - j0) hkpn (by omega), egC kp q'' hkpn (by omega)]
                show entry M 0 (j0 + (l - j0)) + kp * d0i
                  < entry M 0 (j0 + q'') + kp * d0i
                have := h4 (j0 + q'') (by omega) (by omega)
                rw [show j0 + (l - j0) = l from by omega]
                omega)
            rw [hpieq] at this
            unfold entry at this
            rw [egC kp qp hkpn hqpL, egC kp (l - j0) hkpn (by omega)] at this
            rw [show j0 + (l - j0) = l from by omega] at this
            exact this
          rw [hpieq, hpjeq]
          show entry X 2 (j0 + (kp * L + qq)) ≤ entry X 2 (j0 + (kp * L + qp))
          unfold entry
          rw [egC kp qp hkpn hqpL, egC kp qq hkpn hqqL]
          show entry M 2 (j0 + qq) ≤ entry M 2 (j0 + qp)
          by_cases hc0 : kp * d1i = 0
          · -- vanishing lifts: the plain host instance
            have hz' : ∀ (c : Prop) [Decidable c],
                (if c then kp * d1i else 0) = 0 := by
              intro c _
              rw [hc0]
              exact ite_self 0
            rw [hz', hz'] at heqH
            refine h (j0 + qp) (j0 + qq) (by omega) (by omega) hsubH
              (by omega) ?_
            intro l h1 h2 h3 h4
            have := hspH l h1 h2 h3 h4
            rw [hz', hz'] at this
            omega
          by_cases hDp : le1 M j0 (j0 + qp)
          · by_cases hDq : le1 M j0 (j0 + qq)
            · rw [if_pos hDp, if_pos hDq] at heqH
              refine h (j0 + qp) (j0 + qq) (by omega) (by omega) hsubH
                (by omega) ?_
              intro l h1 h2 h3 h4
              have := hspH l h1 h2 h3 h4
              rw [if_pos hDp] at this
              by_cases hDl : le1 M j0 l
              · rw [if_pos hDl] at this
                omega
              · rw [if_neg hDl] at this
                omega
            · exfalso
              rw [if_pos hDp, if_neg hDq] at heqH
              have hw1p : entry M 1 j0 ≤ entry M 1 (j0 + qp) := by
                rcases Nat.eq_zero_or_pos qp with rfl | hqp
                · rw [Nat.add_zero]
                · exact (rtg1_entry1_lt hDp.2.2 (by omega)).le
              obtain ⟨b, hb1, hb2, hb3, hb4⟩ :=
                blocker_of_not_le1 hrtgj0q (by omega) hDq
              rcases Nat.eq_or_lt_of_le (nextrel0_rtrancl_index_le hb2)
                  with rfl | hbq
              · omega
              · have hbD : ¬ le1 M j0 b := by
                  intro hle
                  have := rtg1_entry1_lt hle.2.2 (by omega)
                  omega
                have hbp : j0 + qp < b := by
                  by_contra hcon
                  push Not at hcon
                  have hbrtg : Relation.ReflTransGen (nextrel0 M) b (j0 + qp) :=
                    rtg0_comparable hb2 hrtgpq hcon
                  have := le1_of_chain_le1 hDp (by
                    exact rtg0_comparable hrtgj0q hb2
                      (nextrel0_rtrancl_index_le hb1)) hbrtg
                  exact hbD this
                have := hspH b hbp hbq (by
                    have := le0_interval_gt hb2 (j0 + qq) ⟨by omega, le_rfl⟩
                    omega)
                  (by
                    intro l' hl1 hl2
                    exact le0_interval_gt hb2 l' ⟨hl1, by omega⟩)
                rw [if_pos hDp, if_neg hbD] at this
                omega
          · by_cases hDq : le1 M j0 (j0 + qq)
            · exfalso
              exact hDp (le1_of_chain_le1 hDq hrtgj0p hrtgpq)
            · rw [if_neg hDp, if_neg hDq] at heqH
              refine h (j0 + qp) (j0 + qq) (by omega) (by omega) hsubH
                (by omega) ?_
              intro l h1 h2 h3 h4
              have hDl : ¬ le1 M j0 l := by
                intro hle
                have hrtgpl : Relation.ReflTransGen (nextrel0 M) (j0 + qp) l := by
                  refine rtg0_of_window (by omega) (by omega) ?_
                  intro l'' hl1 hl2
                  exact hsubH l'' hl1 (by omega)
                exact hDp (le1_of_chain_le1 hle hrtgj0p hrtgpl)
              have := hspH l h1 h2 h3 h4
              rw [if_neg hDp, if_neg hDl] at this
              omega
        · -- B2: crossing copies
          rw [hpieq, hpjeq]
          show entry X 2 (j0 + (kq * L + qq)) ≤ entry X 2 (j0 + (kp * L + qp))
          unfold entry
          rw [egC kp qp hkpn hqpL, egC kq qq hkqn hqqL]
          show entry M 2 (j0 + qq) ≤ entry M 2 (j0 + qp)
          by_cases hmk : entry M 2 (j0 + qq) = 0
          · omega
          have hmk1 : (M.getD (j0 + qq) (0, 0, 0)).2.2 = 1 := by
            have := hz2 (j0 + qq) (by omega)
            have e2 : entry M 2 (j0 + qq) = (M.getD (j0 + qq) (0, 0, 0)).2.2 := rfl
            omega
          have hRsub := hsub (j0 + ((kp + 1) * L + 0)) (by
              rw [hpieq]
              have hsm : (kp + 1) * L = kp * L + L := Nat.succ_mul kp L
              omega) (by
              rw [hpjeq]
              have hsm : (kp + 1) * L ≤ kq * L := Nat.mul_le_mul_right L (by omega)
              omega)
          rw [hpieq] at hRsub
          unfold entry at hRsub
          rw [egC kp qp hkpn hqpL, egC (kp + 1) 0 (by omega) (by omega),
            Nat.add_zero] at hRsub
          rw [if_pos (le1_refl hj0b)] at hRsub
          have hRsub' : entry M 0 (j0 + qp) + kp * d0i
              < entry M 0 j0 + (kp + 1) * d0i := hRsub
          have hd0pos : 0 < d0i := by
            by_contra hcon
            push Not at hcon
            have hz0' : d0i = 0 := by omega
            rw [hz0'] at hRsub'
            have hbase : entry M 0 j0 ≤ entry M 0 (j0 + qp) := by
              rcases Nat.eq_zero_or_pos qp with rfl | hq
              · rw [Nat.add_zero]
              · exact (iv (j0 + qp) (by omega) (by omega)).le
            simp only [Nat.mul_zero] at hRsub'
            omega
          have hqplt : entry M 0 (j0 + qp) < entry M 0 j0 + d0i := by
            have hsm : (kp + 1) * d0i = kp * d0i + d0i := Nat.succ_mul kp d0i
            omega
          have heqH : entry M 1 (j0 + qq)
                + (if le1 M j0 (j0 + qq) then kq * d1i else 0)
              = entry M 1 (j0 + qp)
                + (if le1 M j0 (j0 + qp) then kp * d1i else 0) := by
            have := heq
            rw [hpieq, hpjeq] at this
            unfold entry at this
            rw [egC kp qp hkpn hqpL, egC kq qq hkqn hqqL] at this
            exact this
          -- the copy-kq root is right-visible for interior targets
          have hRq : 0 < qq →
              entry M 1 (j0 + qp)
                  + (if le1 M j0 (j0 + qp) then kp * d1i else 0)
                ≤ entry M 1 j0 + kq * d1i := by
            intro hqqpos
            have := hsp (j0 + (kq * L + 0)) (by
                rw [hpieq]
                have h1 : (kp + 1) * L ≤ kq * L := Nat.mul_le_mul_right L (by omega)
                have h2 : (kp + 1) * L = kp * L + L := Nat.succ_mul kp L
                omega) (by
                rw [hpjeq]
                omega) (by
                rw [hpjeq]
                unfold entry
                rw [egC kq 0 hkqn (by omega), egC kq qq hkqn hqqL, Nat.add_zero]
                show entry M 0 j0 + kq * d0i < entry M 0 (j0 + qq) + kq * d0i
                have := iv (j0 + qq) (by omega) (by omega)
                omega) (by
                intro l'' hl1 hl2
                rw [hpjeq] at hl2
                have hlq : ∃ q'', 0 < q'' ∧ q'' < qq
                    ∧ l'' = j0 + (kq * L + q'') :=
                  ⟨l'' - j0 - kq * L, by omega, by omega, by omega⟩
                obtain ⟨q'', hq1, hq2, rfl⟩ := hlq
                unfold entry
                rw [egC kq 0 hkqn (by omega), egC kq q'' hkqn (by omega),
                  Nat.add_zero]
                show entry M 0 j0 + kq * d0i < entry M 0 (j0 + q'') + kq * d0i
                have := iv (j0 + q'') (by omega) (by omega)
                omega)
            rw [hpieq] at this
            unfold entry at this
            rw [egC kp qp hkpn hqpL, egC kq 0 hkqn (by omega), Nat.add_zero] at this
            rw [if_pos (le1_refl hj0b)] at this
            exact this
          by_cases hd1z : d1i = 0
          · -- `t = 1`: the source is forced onto the root; host instance
            have hze : ∀ (c : Prop) [Decidable c] (k'' : ℕ),
                (if c then k'' * d1i else 0) = 0 := by
              intro c _ k''
              rw [hd1z, Nat.mul_zero]
              exact ite_self 0
            rw [hze, hze] at heqH
            have hsrow1 : srow M (M.length - 1) = 1 := by
              have h0 : 0 < srow M (M.length - 1) := by
                by_contra hcon
                push Not at hcon
                rw [hd0i, if_neg (by omega)] at hd0pos
                omega
              by_cases h2' : 1 < srow M (M.length - 1)
              · exfalso
                have np2 : nextrel2 M j0 (M.length - 1) := by
                  have np' := np
                  unfold nextR at np'
                  rw [if_neg (by omega : ¬ srow M (M.length - 1) = 0),
                    if_neg (by omega : ¬ srow M (M.length - 1) = 1)] at np'
                  exact np'
                have hgt := rtg1_entry1_lt np2.2.2.2.2.1.2.2 (by omega)
                rw [hd1i, if_pos h2'] at hd1z
                omega
              · omega
            have np1 : nextrel1 M j0 (M.length - 1) := by
              have np' := np
              unfold nextR at np'
              rw [if_neg (by omega : ¬ srow M (M.length - 1) = 0),
                if_pos hsrow1] at np'
              exact np'
            have hlp1 : entry M 1 (M.length - 1) = entry M 1 j0 + 1 :=
              nextrel1_snd_succ hr np1
            have hlp0 : entry M 0 (M.length - 1) = entry M 0 j0 + d0i := by
              rw [hd0i, if_pos (by omega)]
              have := iv (M.length - 1) j0lt le_rfl
              omega
            have hqp0 : qp = 0 := by
              by_contra hqppos
              push Not at hqppos
              have hvis : le0 M (j0 + qp) (M.length - 1) := by
                refine ⟨by omega, by omega, ?_⟩
                refine rtg0_of_window (by omega) (by omega) ?_
                intro l hl1 hl2
                rcases Nat.eq_or_lt_of_le hl2 with rfl | hl3
                · omega
                · -- inside the block: the X subtree covers it at copy kp
                  have := hsub (j0 + (kp * L + (l - j0))) (by
                      rw [hpieq]
                      omega) (by
                      rw [hpjeq]
                      have h5 : (kp + 1) * L ≤ kq * L :=
                        Nat.mul_le_mul_right L (by omega)
                      have h6 : (kp + 1) * L = kp * L + L := Nat.succ_mul kp L
                      omega)
                  rw [hpieq] at this
                  unfold entry at this
                  rw [egC kp qp hkpn hqpL, egC kp (l - j0) hkpn (by omega)] at this
                  rw [show j0 + (l - j0) = l from by omega] at this
                  have this' : entry M 0 (j0 + qp) + kp * d0i
                      < entry M 0 l + kp * d0i := this
                  omega
              have := np1.2.2.2.2.2 (j0 + qp) ⟨by omega, hvis⟩
              rcases Nat.eq_zero_or_pos qq with rfl | hqqpos
              · simp only [Nat.add_zero] at heqH
                omega
              · have := hRq hqqpos
                rw [hze] at this
                have hkq0 : kq * d1i = 0 := by
                  rw [hd1z]
                  exact Nat.mul_zero kq
                omega
            subst hqp0
            rw [Nat.add_zero] at heqH ⊢
            rcases Nat.eq_zero_or_pos qq with rfl | hqqpos
            · rw [Nat.add_zero]
            · refine h j0 (j0 + qq) (by omega) (by omega) ?_ heqH ?_
              · intro l h1 h2
                exact iv l (by omega) (by omega)
              · intro l h1 h2 h3 h4
                have := hsp (j0 + (kq * L + (l - j0))) (by
                    rw [hpieq]
                    have h5 : (kp + 1) * L ≤ kq * L :=
                      Nat.mul_le_mul_right L (by omega)
                    have h6 : (kp + 1) * L = kp * L + L := Nat.succ_mul kp L
                    omega) (by
                    rw [hpjeq]
                    omega) (by
                    rw [hpjeq]
                    unfold entry
                    rw [egC kq (l - j0) hkqn (by omega), egC kq qq hkqn hqqL]
                    show entry M 0 (j0 + (l - j0)) + kq * d0i
                      < entry M 0 (j0 + qq) + kq * d0i
                    rw [show j0 + (l - j0) = l from by omega]
                    omega) (by
                    intro l'' hl1 hl2
                    rw [hpjeq] at hl2
                    have hlq : ∃ q'', l - j0 < q'' ∧ q'' < qq
                        ∧ l'' = j0 + (kq * L + q'') :=
                      ⟨l'' - j0 - kq * L, by omega, by omega, by omega⟩
                    obtain ⟨q'', hq1, hq2, rfl⟩ := hlq
                    unfold entry
                    rw [egC kq (l - j0) hkqn (by omega),
                      egC kq q'' hkqn (by omega)]
                    show entry M 0 (j0 + (l - j0)) + kq * d0i
                      < entry M 0 (j0 + q'') + kq * d0i
                    have := h4 (j0 + q'') (by omega) (by omega)
                    rw [show j0 + (l - j0) = l from by omega]
                    omega)
                rw [hpieq] at this
                unfold entry at this
                rw [egC kp 0 hkpn (by omega), egC kq (l - j0) hkqn (by omega),
                  Nat.add_zero] at this
                rw [show j0 + (l - j0) = l from by omega] at this
                have this' : entry M 1 j0
                    + (if le1 M j0 j0 then kp * d1i else 0)
                    ≤ entry M 1 l + (if le1 M j0 l then kq * d1i else 0) := this
                rw [hze, hze] at this'
                omega
          · -- `t = 2`: a marked crossing target is impossible
            exfalso
            have hd1pos : 0 < d1i := by omega
            have hi2 : 1 < srow M (M.length - 1) := by
              by_contra hcon
              push Not at hcon
              rw [hd1i, if_neg (by omega)] at hd1z
              omega
            have np2 : nextrel2 M j0 (M.length - 1) := by
              have np' := np
              unfold nextR at np'
              rw [if_neg (by omega : ¬ srow M (M.length - 1) = 0),
                if_neg (by omega : ¬ srow M (M.length - 1) = 1)] at np'
              exact np'
            have hj00 : entry M 2 j0 = 0 := by
              have h2lt := np2.2.2.2.1
              have := hz2 (M.length - 1) (by omega)
              have e2a : entry M 2 j0 = (M.getD j0 (0, 0, 0)).2.2 := rfl
              have e2b : entry M 2 (M.length - 1)
                = (M.getD (M.length - 1) (0, 0, 0)).2.2 := rfl
              omega
            have hqqpos : 0 < qq := by
              by_contra hq0
              push Not at hq0
              have he : qq = 0 := by omega
              subst he
              rw [Nat.add_zero] at hmk
              exact hmk hj00
            have hRq' := hRq hqqpos
            by_cases hDq : le1 M j0 (j0 + qq)
            · -- lifted marked target: the root spine caps it
              rw [if_pos hDq] at heqH
              have hgt := rtg1_entry1_lt hDq.2.2 (by omega)
              have hsm : kp * d1i ≤ kq * d1i :=
                Nat.mul_le_mul_right d1i (by omega)
              by_cases hDp : le1 M j0 (j0 + qp)
              · rw [if_pos hDp] at heqH hRq'
                have hgtp : entry M 1 j0 ≤ entry M 1 (j0 + qp) := by
                  rcases Nat.eq_zero_or_pos qp with rfl | hqp
                  · rw [Nat.add_zero]
                  · exact (rtg1_entry1_lt hDp.2.2 (by omega)).le
                omega
              · rw [if_neg hDp] at heqH hRq'
                omega
            · -- unlifted marked target
              rw [if_neg hDq] at heqH
              have hlp0 : entry M 0 (M.length - 1) = entry M 0 j0 + d0i := by
                rw [hd0i, if_pos (by omega)]
                have := iv (M.length - 1) j0lt le_rfl
                omega
              -- the source is a chain node of the dropped column
              have hqvis : Relation.ReflTransGen (nextrel0 M) (j0 + qp)
                  (M.length - 1) := by
                refine rtg0_of_window (by omega) (by omega) ?_
                intro l hl1 hl2
                rcases Nat.eq_or_lt_of_le hl2 with rfl | hl3
                · omega
                · have := hsub (j0 + (kp * L + (l - j0))) (by
                      rw [hpieq]
                      omega) (by
                      rw [hpjeq]
                      have h5 : (kp + 1) * L ≤ kq * L :=
                        Nat.mul_le_mul_right L (by omega)
                      have h6 : (kp + 1) * L = kp * L + L := Nat.succ_mul kp L
                      omega)
                  rw [hpieq] at this
                  unfold entry at this
                  rw [egC kp qp hkpn hqpL, egC kp (l - j0) hkpn (by omega)] at this
                  rw [show j0 + (l - j0) = l from by omega] at this
                  have this' : entry M 0 (j0 + qp) + kp * d0i
                      < entry M 0 l + kp * d0i := this
                  omega
              have hblocker : entry M 1 j0 < entry M 1 (j0 + qq) → False := by
                intro hq1gt
                obtain ⟨b, hb1, hb2, hb3, hb4⟩ :=
                  blocker_of_not_le1 (le0_interval_desc chain (by omega)
                    (j0 + qq) (by omega) (by omega)) (by omega) hDq
                rcases Nat.eq_or_lt_of_le (nextrel0_rtrancl_index_le hb2)
                    with rfl | hbq
                · omega
                · have hbj0 : j0 < b := by
                    have := nextrel0_rtrancl_index_le hb1
                    rcases Nat.eq_or_lt_of_le this with rfl | h'
                    · exact absurd rfl hb3
                    · exact h'
                  have hbD : ¬ le1 M j0 b := by
                    intro hle
                    have := rtg1_entry1_lt hle.2.2 (by omega)
                    omega
                  have := hsp (j0 + (kq * L + (b - j0))) (by
                      rw [hpieq]
                      have h5 : (kp + 1) * L ≤ kq * L :=
                        Nat.mul_le_mul_right L (by omega)
                      have h6 : (kp + 1) * L = kp * L + L := Nat.succ_mul kp L
                      omega) (by
                      rw [hpjeq]
                      omega) (by
                      rw [hpjeq]
                      unfold entry
                      rw [egC kq (b - j0) hkqn (by omega), egC kq qq hkqn hqqL]
                      show entry M 0 (j0 + (b - j0)) + kq * d0i
                        < entry M 0 (j0 + qq) + kq * d0i
                      have := le0_interval_gt hb2 (j0 + qq) ⟨by omega, le_rfl⟩
                      rw [show j0 + (b - j0) = b from by omega]
                      omega) (by
                      intro l'' hl1 hl2
                      rw [hpjeq] at hl2
                      have hlq : ∃ q'', b - j0 < q'' ∧ q'' < qq
                          ∧ l'' = j0 + (kq * L + q'') :=
                        ⟨l'' - j0 - kq * L, by omega, by omega, by omega⟩
                      obtain ⟨q'', hq1, hq2, rfl⟩ := hlq
                      unfold entry
                      rw [egC kq (b - j0) hkqn (by omega),
                        egC kq q'' hkqn (by omega)]
                      show entry M 0 (j0 + (b - j0)) + kq * d0i
                        < entry M 0 (j0 + q'') + kq * d0i
                      have := le0_interval_gt hb2 (j0 + q'') ⟨by omega, by omega⟩
                      rw [show j0 + (b - j0) = b from by omega]
                      omega)
                  rw [hpieq] at this
                  unfold entry at this
                  rw [egC kp qp hkpn hqpL, egC kq (b - j0) hkqn (by omega)] at this
                  rw [show j0 + (b - j0) = b from by omega] at this
                  have this' : entry M 1 (j0 + qp)
                      + (if le1 M j0 (j0 + qp) then kp * d1i else 0)
                      ≤ entry M 1 b + (if le1 M j0 b then kq * d1i else 0) := this
                  rw [if_neg hbD] at this'
                  by_cases hDp : le1 M j0 (j0 + qp)
                  · rw [if_pos hDp] at this' heqH
                    omega
                  · rw [if_neg hDp] at this' heqH
                    omega

              by_cases hqp0 : 0 < qp
              · have hRTGj0qp : Relation.ReflTransGen (nextrel0 M) j0 (j0 + qp) :=
                  rtg0_comparable chain hqvis (by omega)
                have hbnd := le1_chain_window np2.2.2.2.2.1.2.2 (j0 + qp)
                  hRTGj0qp hqvis (by omega)
                refine hblocker ?_
                by_cases hDp : le1 M j0 (j0 + qp)
                · rw [if_pos hDp] at heqH
                  omega
                · rw [if_neg hDp] at heqH
                  omega
              · -- source at the root: forced onto the host instance
                push Not at hqp0
                have hqp00 : qp = 0 := by omega
                subst hqp00
                simp only [Nat.add_zero] at heqH
                rw [if_pos (le1_refl hj0b)] at heqH
                have hle' : entry M 1 (j0 + qq) ≤ entry M 1 j0 := by
                  by_contra hcon
                  push Not at hcon
                  exact hblocker hcon
                have hkp0 : kp * d1i = 0 ∧ entry M 1 (j0 + qq) = entry M 1 j0 := by
                  constructor <;> omega
                -- host instance rooted at the block root
                have hcontra := h j0 (j0 + qq) (by omega) (by omega)
                  (fun l h1 h2 => iv l (by omega) (by omega)) hkp0.2 ?_
                · have e2a : entry M 2 j0 = (M.getD j0 (0, 0, 0)).2.2 := rfl
                  omega
                · intro l h1 h2 h3 h4
                  have hlrtg : Relation.ReflTransGen (nextrel0 M) l (j0 + qq) := by
                    refine rtg0_of_window (by omega) (by omega) ?_
                    intro l'' hl1 hl2
                    rcases Nat.eq_or_lt_of_le hl2 with rfl | hl3
                    · exact h3
                    · exact h4 l'' hl1 hl3
                  have := hsp (j0 + (kq * L + (l - j0))) (by
                      rw [hpieq]
                      have h5 : (kp + 1) * L ≤ kq * L :=
                        Nat.mul_le_mul_right L (by omega)
                      have h6 : (kp + 1) * L = kp * L + L := Nat.succ_mul kp L
                      omega) (by
                      rw [hpjeq]
                      omega) (by
                      rw [hpjeq]
                      unfold entry
                      rw [egC kq (l - j0) hkqn (by omega), egC kq qq hkqn hqqL]
                      show entry M 0 (j0 + (l - j0)) + kq * d0i
                        < entry M 0 (j0 + qq) + kq * d0i
                      rw [show j0 + (l - j0) = l from by omega]
                      omega) (by
                      intro l'' hl1 hl2
                      rw [hpjeq] at hl2
                      have hlq : ∃ q'', l - j0 < q'' ∧ q'' < qq
                          ∧ l'' = j0 + (kq * L + q'') :=
                        ⟨l'' - j0 - kq * L, by omega, by omega, by omega⟩
                      obtain ⟨q'', hq1, hq2, rfl⟩ := hlq
                      unfold entry
                      rw [egC kq (l - j0) hkqn (by omega),
                        egC kq q'' hkqn (by omega)]
                      show entry M 0 (j0 + (l - j0)) + kq * d0i
                        < entry M 0 (j0 + q'') + kq * d0i
                      have := h4 (j0 + q'') (by omega) (by omega)
                      rw [show j0 + (l - j0) = l from by omega]
                      omega)
                  rw [hpieq] at this
                  unfold entry at this
                  rw [egC kp 0 hkpn (by omega), egC kq (l - j0) hkqn (by omega),
                    Nat.add_zero] at this
                  rw [show j0 + (l - j0) = l from by omega] at this
                  have this' : entry M 1 j0
                      + (if le1 M j0 j0 then kp * d1i else 0)
                      ≤ entry M 1 l + (if le1 M j0 l then kq * d1i else 0) := this
                  rw [if_pos (le1_refl hj0b)] at this'
                  by_cases hDl : le1 M j0 l
                  · rw [if_pos hDl] at this'
                    have := rtg1_entry1_lt hDl.2.2 (by omega)
                    omega
                  · rw [if_neg hDl] at this'
                    omega

/-- **The z-jump prohibition on standard forms.** -/
theorem zjump_ST_TS {M : TrioSeq} (h : ST_TS M) : zjump M := by
  induction h with
  | diag v => exact zjump_diagSeqT v
  | oper hN hn ih =>
    exact zjump_oper hn (r1ok_ST_TS hN) (z2ok_ST_TS hN) (markP1_ST_TS hN) ih

end Googology.Trans.BMS.TrioCof
