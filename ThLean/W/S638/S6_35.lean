import ThLean.BP.S6.Descent

noncomputable section
open scoped BigOperators
open ThLean.BP.S6

namespace ThLean.W.S638

theorem S6_35Statement_holds : ThLean.BP.S6.S6_35Statement := by
  unfold ThLean.BP.S6.S6_35Statement
  intro M a b ha hb hrec
  have hmain : ∀ j w m, w < j → j ≤ m → m < M →
      a m j ≤ (∑ k ∈ Finset.Ico (w + 1) (j + 1),
        alpha ^ (j - k) * b (m - j + k) k) +
        alpha ^ (j - w) * a (m - j + w) w := by
    intro j
    induction j with
    | zero => intro w m hwj hjm hm; omega
    | succ j ih =>
      intro w m hwj hjm hm
      by_cases hw : w = j
      · subst w
        have hstep := hrec m (j + 1) (by omega) hjm hm
        have htime : m - (j + 1) + j = m - 1 := by omega
        have htime' : m - (j + 1) + (j + 1) = m := by omega
        simpa [htime, htime', Nat.sub_self] using hstep
      · have hw' : w < j := by omega
        have hstep := hrec m (j + 1) (by omega) hjm hm
        have hi := ih w (m - 1) hw' (by omega) (by omega)
        have hα : 0 ≤ alpha := by norm_num [alpha]
        have hsum : alpha *
            (∑ k ∈ Finset.Ico (w + 1) (j + 1),
              alpha ^ (j - k) * b ((m - 1) - j + k) k) =
            ∑ k ∈ Finset.Ico (w + 1) (j + 1),
              alpha ^ (j + 1 - k) * b (m - (j + 1) + k) k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          have hk' := Finset.mem_Ico.mp hk
          have hexp : j + 1 - k = (j - k) + 1 := by omega
          have htime : (m - 1) - j + k = m - (j + 1) + k := by omega
          rw [hexp, pow_succ, htime]
          ring
        have hbase : alpha *
            (alpha ^ (j - w) * a ((m - 1) - j + w) w) =
            alpha ^ (j + 1 - w) * a (m - (j + 1) + w) w := by
          have hexp : j + 1 - w = (j - w) + 1 := by omega
          have htime : (m - 1) - j + w = m - (j + 1) + w := by omega
          rw [hexp, pow_succ, htime]
          ring
        calc
          a m (j + 1) ≤ b m (j + 1) + alpha * a (m - 1) j := hstep
          _ ≤ b m (j + 1) + alpha *
              ((∑ k ∈ Finset.Ico (w + 1) (j + 1),
                alpha ^ (j - k) * b ((m - 1) - j + k) k) +
                alpha ^ (j - w) * a ((m - 1) - j + w) w) := by
            calc
              _ = alpha * a (m - 1) j + b m (j + 1) := by ring
              _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left hi hα) _
              _ = _ := by ring
          _ = (∑ k ∈ Finset.Ico (w + 1) (j + 2),
                alpha ^ (j + 1 - k) * b (m - (j + 1) + k) k) +
                alpha ^ (j + 1 - w) * a (m - (j + 1) + w) w := by
            calc
              _ = b m (j + 1) +
                  (alpha * (∑ k ∈ Finset.Ico (w + 1) (j + 1),
                    alpha ^ (j - k) * b ((m - 1) - j + k) k) +
                   alpha * (alpha ^ (j - w) * a ((m - 1) - j + w) w)) := by rw [mul_add]
              _ = b m (j + 1) +
                  ((∑ k ∈ Finset.Ico (w + 1) (j + 1),
                    alpha ^ (j + 1 - k) * b (m - (j + 1) + k) k) +
                   alpha ^ (j + 1 - w) * a (m - (j + 1) + w) w) := by rw [hsum, hbase]
              _ = _ := by
                have htime : m - (j + 1) + (j + 1) = m := by omega
                conv_rhs => rw [Finset.sum_Ico_succ_top (by omega)]
                simp only [Nat.sub_self, pow_zero, one_mul]
                rw [htime]
                ring
  intro w j m hwj hjm hm
  exact hmain j w m hwj hjm hm

end ThLean.W.S638
