import ThLean.W.SA27S.TripleSeries
import ThLean.W.SA27S.GraphSupports
import ThLean.W.SA27.Interpolation

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA27S
open ThresholdFoundations ThLean.BP.SA

/-- Close the count-histogram expansion left open in the SA27 attempt. -/
theorem markedInterpolationExpansion (h10 : SA_I10Statement) (h11a : SA_I11aStatement) :
    ThLean.Contrib.SA27.MarkedInterpolationExpansionStatement h10 h11a := by
  intro q n₁ n₂ hq hn₁ hn₂ μ
  let : Nonempty (Fin n₁) := ⟨⟨0, by omega⟩⟩
  let : Nonempty (Fin n₂) := ⟨⟨0, by omega⟩⟩
  let : Nonempty (Fin (n₁ + n₂)) := ⟨⟨0, by omega⟩⟩
  let A := Endpoints (n₁ + n₂)
  let B := Endpoints n₁
  let C := Endpoints n₂
  let e := taggedCountsEquiv A B C
  let F : TripleCounts A B C → ℝ := fun z =>
    indicator (Colorable q (ThresholdFoundations.supportGraph interpolationMarkEdge
      (Finset.univ.filter (fun d => 0 < e.symm z d))))
  let w := tripleWeight (prefixWeight A (μ 0)) (prefixWeight B (μ 1))
    (prefixWeight C (μ 2))
  let v := tripleWeight (countWeight A (μ 0)) (countWeight B (μ 1))
    (countWeight C (μ 2))
  have hsource : (∑' p : InterpolationPrefix n₁ n₂,
      w p * indicator (Colorable q (prefixMixedGraph p))) = chiBar q n₁ n₂ μ := by
    exact triplePrefix_mean A B C μ
      (fun p => indicator (Colorable q (prefixMixedGraph p))) (fun _ => indicator_norm_le _)
  have hhist : (∑' p : InterpolationPrefix n₁ n₂, w p * F (tripleHistogram p)) =
      ∑' z : TripleCounts A B C, v z * F z :=
    tripleHistogram_mean h11a A B C μ F (fun _ => indicator_norm_le _)
  calc
    chiBar q n₁ n₂ μ = ∑' p : InterpolationPrefix n₁ n₂,
        w p * indicator (Colorable q (prefixMixedGraph p)) := hsource.symm
    _ = ∑' p : InterpolationPrefix n₁ n₂, w p * F (tripleHistogram p) := by
      apply tsum_congr
      intro p
      exact congrArg (fun t => w p * t) (prefixColorable_histogram h10 q n₁ n₂ hq p)
    _ = ∑' z : TripleCounts A B C, v z * F z := hhist
    _ = ∑' z : InterpolationMark n₁ n₂ → ℕ, v (e z) * F (e z) :=
      (e.tsum_eq (fun z => v z * F z)).symm
    _ = _ := by
      apply tsum_congr
      intro z
      have hF : F (e z) = indicator (Colorable q
          (ThresholdFoundations.supportGraph interpolationMarkEdge
            (Finset.univ.filter (fun d => 0 < z d)))) := by
        dsimp only [F]
        rw [e.symm_apply_apply]
      rw [hF]
      congr 1
      simp [v, tripleWeight, countWeight, e, taggedCountsEquiv,
        A, B, C, Endpoints, interpolationMarkRate, Fintype.prod_sum_type,
        Fintype.card_prod, Nat.cast_mul, pow_two]

/-- Absolute convergence and equality with the frozen finite-support extension,
using only the three sibling leaves listed in the blueprint. -/
theorem SA_I13aStatement_of_deps
    (h10 : SA_I10Statement) (h11a : SA_I11aStatement) (h11b : SA_I11bStatement) :
    ThLean.BP.SA.SA_I13aStatement :=
  ThLean.W.SA27.SA_I13aStatement_from_marked_expansion h10 h11a h11b
    (markedInterpolationExpansion h10 h11a)

example (h10 : SA_I10Statement) (h11a : SA_I11aStatement) (h11b : SA_I11bStatement) :
    ThLean.BP.SA.SA_I13aStatement := SA_I13aStatement_of_deps h10 h11a h11b

end ThLean.W.SA27S
