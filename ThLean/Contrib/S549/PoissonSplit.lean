import ThLean.BP.S5.Poisson

noncomputable section
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.Contrib.S549
open ThresholdFoundations ThLean.BP.S5

/-- Finite-coordinate factorization of the independent Poisson graph law
across a finite partition. -/
def S549_CountMeanPartitionFactorizationStatement : Prop :=
  ∀ (V : Type) [Fintype V] (A B : Type) [Fintype A] [Fintype B]
    (e : A ⊕ B ≃ V), 3 ≤ Fintype.card V → 2 ≤ Fintype.card B →
    ∀ (r : ℝ), 0 ≤ r → ∀ f : MGraph V → ℝ,
      (∃ C : ℝ, ∀ G, |f G| ≤ C) →
      countMean r f =
        countMean r
          (fun GB : MGraph B =>
            countMean r
              (fun GA : MGraph A =>
                ∑' c : (A × B) → ℕ,
                  (∏ p, poissonWeight r (c p)) *
                    f (mapGraph (fun b => e (Sum.inr b)) GB +
                      mapGraph (fun a => e (Sum.inl a)) GA +
                      (fun edge : Sym2 V =>
                        ∑ p : A × B, if edge = s(e (Sum.inl p.1), e (Sum.inr p.2))
                          then c p else 0))))

end ThLean.Contrib.S549
