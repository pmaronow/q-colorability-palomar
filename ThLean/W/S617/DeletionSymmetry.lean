import ThLean.BP.S6.Deletion

noncomputable section
open scoped BigOperators
open ThLean.BP.S6
open ThresholdFoundations
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S617

theorem S6_15Statement_of_deps
    (h07 : ThLean.BP.S6.S6_07Statement) :
    ThLean.BP.S6.S6_15Statement := by
  intro n q m j hn hq hj u
  classical
  let f : Fin n → ThLean.BP.S6.Graph n → ℝ := fun a G =>
    indicator (degree G a = j - 1) * beta q G a
  have hmean_sum :
      meanGraph m (fun G => ∑ a : Fin n, f a G) =
        ∑ a : Fin n, meanGraph m (f a) := by
    unfold meanGraph ThresholdFoundations.uniformMean
    rw [Finset.sum_comm, Finset.sum_div]
  have hvertex (a : Fin n) :
      meanGraph m (f a) = meanGraph m (f u) := by
    let π : Equiv.Perm (Fin n) := Equiv.swap u a
    have hπ : π u = a := by simp [π]
    have hmean := (h07 n q hn hq π (fun _ => 0) u (j - 1) 1 (by omega)).2.2.2.2.2.2.2.2.1
    have htransport (H : ThLean.BP.S6.Graph n) :
        f a (relabel π H) = f u H := by
      have hcov := h07 n q hn hq π H u (j - 1) 1 (by omega)
      rcases hcov with ⟨_, hdegree, _, _, hbeta, _, _, _, _, _⟩
      dsimp [f]
      rw [← hπ, hdegree, hbeta]
    calc
      meanGraph m (f a) = meanGraph m (fun H => f a (relabel π H)) := by
        exact (hmean m (f a)).symm
      _ = meanGraph m (f u) := by
        congr 1
        funext H
        exact htransport H
  have hsum :
      meanGraph m (fun G => ∑ a : Fin n, f a G) =
        (n : ℝ) * meanGraph m (f u) := by
    rw [hmean_sum]
    simp_rw [hvertex]
    simp
  simpa [f, rootEqMean] using hsum

end ThLean.W.S617
