import ThLean.BP.S3.Cycles

noncomputable section
universe u

namespace ThLean.Contrib.S370

open ThresholdFoundations ThLean.BP.S3

/-- The decoding half of S3-67: an exact dumbbell admits a canonical code whose
labels list its support vertices. -/
def S3_67DecodeStatement : Prop :=
  ∀ (V : Type u) [Fintype V],
  ∀ G : MGraph V, ExactDumbbell G →
    let k := (vertexSupport G).card
    2 ≤ k ∧ edgeCount G = k+1 ∧
    ∃ (hk : 0 < k) (j₁ j₂ j₃ : ℕ) (v : Fin k ↪ V),
      2 ≤ j₁ ∧ 2 ≤ j₂ ∧ j₁+j₂+j₃ = k+1 ∧
      G = dumbbellCode hk j₁ j₂ j₃ v

/-- The construction half of S3-67: every valid dumbbell code has the intended
exact support, shape, and number of occurrences. -/
def S3_67CodeStatement : Prop :=
  ∀ (V : Type u) [Fintype V],
  ∀ (k : ℕ) (hk : 0 < k) (j₁ j₂ j₃ : ℕ) (v : Fin k ↪ V),
    2 ≤ k → 2 ≤ j₁ → 2 ≤ j₂ → j₁+j₂+j₃ = k+1 →
    ExactDumbbell (dumbbellCode hk j₁ j₂ j₃ v) ∧
      (vertexSupport (dumbbellCode hk j₁ j₂ j₃ v)).card = k ∧
      edgeCount (dumbbellCode hk j₁ j₂ j₃ v) = k+1

theorem occurrence_card_eq_edgeCount {V : Type u} [Fintype V] (G : MGraph V) :
    Fintype.card (Occurrence G) = edgeCount G := by
  classical
  simp [Occurrence, edgeCount, Fintype.card_sigma]

end ThLean.Contrib.S370
