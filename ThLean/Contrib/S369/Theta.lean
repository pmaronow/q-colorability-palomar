import ThLean.BP.S3.Cycles

noncomputable section
open scoped BigOperators
universe u
namespace ThLean.Contrib.S369
open ThresholdFoundations
open ThLean.BP.S3

/-- Decode the path data of an exact theta as the canonical three-path code. -/
def ThetaExactDecodeStatement : Prop :=
  ∀ (V : Type u) [Fintype V],
  ∀ G : MGraph V, ExactTheta G →
    let k := (vertexSupport G).card
    2 ≤ k ∧ edgeCount G = k+1 ∧
    ∃ (hk : 0 < k) (j₁ j₂ j₃ : ℕ) (v : Fin k ↪ V),
      1 ≤ j₁ ∧ 1 ≤ j₂ ∧ 1 ≤ j₃ ∧ j₁+j₂+j₃ = k+1 ∧
      G = thetaCode hk j₁ j₂ j₃ v

/-- The canonical three-path code is an exact theta under the path constraints. -/
def ThetaCodeExactStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (k : ℕ) (hk : 0 < k)
    (j₁ j₂ j₃ : ℕ) (v : Fin k ↪ V),
    2 ≤ k → 1 ≤ j₁ → 1 ≤ j₂ → 1 ≤ j₃ → j₁+j₂+j₃ = k+1 →
    ExactTheta (thetaCode hk j₁ j₂ j₃ v)

/-- The support of the canonical code consists of exactly its `k` labels. -/
def ThetaCodeSupportStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (k : ℕ) (hk : 0 < k)
    (j₁ j₂ j₃ : ℕ) (v : Fin k ↪ V),
    2 ≤ k → 1 ≤ j₁ → 1 ≤ j₂ → 1 ≤ j₃ → j₁+j₂+j₃ = k+1 →
    (vertexSupport (thetaCode hk j₁ j₂ j₃ v)).card = k

end ThLean.Contrib.S369
