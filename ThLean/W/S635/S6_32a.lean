import ThLean.BP.S6.Descent
import ThLean.Contrib.S635.S6_32aHelpers

set_option maxHeartbeats 1000000

noncomputable section
open scoped BigOperators ENNReal
open ThresholdFoundations ThLean.BP.S6 ThLean.Contrib.S635
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S635

lemma uniformMean_inst_irrel {A : Type*} (i j : Fintype A) (f : A → ℝ) :
    @uniformMean A i f = @uniformMean A j f := by
  unfold uniformMean
  have hcard : @Fintype.card A i = @Fintype.card A j :=
    @Fintype.card_congr A A i j (Equiv.refl A)
  have hsum : (@Finset.univ A i).sum f = (@Finset.univ A j).sum f := by
    exact @Fintype.sum_equiv A A ℝ i j _ (Equiv.refl A) f f (fun _ => rfl)
  rw [hsum, hcard]

lemma meanGraph_eq_graphMean {n m : ℕ} (f : Graph n → ℝ) :
    meanGraph (n := n) m f = graphMean (V := Fin n) m f := by
  unfold meanGraph graphMean
  apply uniformMean_inst_irrel

/-- The terminal bridge and total finite hazard budget, modulo the two
explicit first-failure identities in `ThLean.Contrib.S635`. -/
theorem S6_32aStatement_of_helpers
    (hterminal : S6_32aTerminalIdentityStatement)
    (hhazard : ThresholdFoundations.PreHazardStatement)
    (hevent : S6_32aHazardEventIdentityStatement) :
    ThLean.BP.S6.S6_32aStatement := by
  intro n q M D hn hq
  have hpre := hhazard q n hq (by omega)
  have hunit := hpre.2.1 (Finset.range M) (fun _ _ => (1 : ℝ)) (by
    intro m hm G
    constructor <;> norm_num)
  have htotal :
      (∑ m ∈ Finset.range M, meanGraph (n := n) m (kappa q)) ≤ 1 := by
    calc
      (∑ m ∈ Finset.range M, meanGraph (n := n) m (kappa q)) ≤
          ∑ m ∈ Finset.range M, hittingMass (V := Fin n) q m := by
        have hgraph :
            (∑ m ∈ Finset.range M, graphMean (V := Fin n) m (kappa q)) ≤
              ∑ m ∈ Finset.range M, hittingMass (V := Fin n) q m := by
          simpa only [one_mul] using hunit
        have hmean :
            (∑ m ∈ Finset.range M, meanGraph (n := n) m (kappa q)) =
              ∑ m ∈ Finset.range M, graphMean (V := Fin n) m (kappa q) := by
          apply Finset.sum_congr rfl
          intro m hm
          exact meanGraph_eq_graphMean (n := n) (m := m) (f := kappa q)
        rw [hmean]
        exact hgraph
      _ ≤ 1 := hpre.2.2 (Finset.range M)
  exact ⟨hterminal n q M D hn hq, htotal, hevent n q M hn hq⟩

end ThLean.W.S635
