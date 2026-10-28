import ThLean.BP.S5.Support

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.BP.S5
open ThresholdFoundations

/-- P3-LOW-01 helper; lem:low-frozen(i): coloring a graph with an added root. -/
def S5_01AStatement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 3 ≤ q →
  ∀ (B : MGraph V) (xs : List V) (τ : Option V → Fin q),
    IsColoring q (addRoot B xs) τ ↔
      IsColoring q B (fun v => τ (some v)) ∧ ∀ v ∈ xs, τ none ≠ τ (some v)

/-- P3-LOW-01; lem:low-frozen(i): occurrence-preserving deletion and extension. -/
def S5_01Statement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 3 ≤ q →
  ∀ (G : MGraph V), Loopless G → ∀ a : V,
    (∃ xs : List (Outside a), xs.length = degree G a ∧ G = rebuild G a xs) ∧
    (∀ xs : List (Outside a), G = rebuild G a xs → ∀ τ : V → Fin q,
      IsColoring q G τ ↔
        IsColoring q (outsideGraph G a) (fun v => τ v.val) ∧
          τ a ∉ (xs.map (fun v => τ v.val)).toFinset)

/-- P3-LOW-02; lem:low-frozen(ii): a fresh root edge detects freezing. -/
def S5_02Statement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 3 ≤ q →
  ∀ (B : MGraph V), Loopless B → ∀ (xs : List V) (b : V),
    Colorable q (addRoot B xs) →
    (Frozen q (addRoot B xs) none (some b) ↔
      ¬ Colorable q (addRoot B (xs ++ [b])))

/-- P3-LOW-03; lem:low-frozen(iii): all background colorings meet the palette bound. -/
def S5_03Statement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 3 ≤ q →
  ∀ (G : MGraph V), Loopless G → ∀ (a b : V), a ≠ b → Frozen q G a b →
  ∀ xs : List (Outside a), G = rebuild G a xs →
    Colorable q (outsideGraph G a) ∧
    (∀ σ, IsColoring q (outsideGraph G a) σ → q - 1 ≤ (xs.map σ).toFinset.card) ∧
    neverMonochromatic q (outsideGraph G a) xs ∧ 2 ≤ xs.length

/-- P3-LOW-04; lem:low-frozen(iv): pullback is a bijection, also with loops. -/
def S5_04Statement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 3 ≤ q →
  ∀ (F : MGraph V) (Z : Finset V), Z.Nonempty →
    (∃ E : {τ // IsColoring q (identify F Z) τ} ≃
        {σ // IsColoring q F σ ∧ constantOn σ Z},
      ∀ τ, (E τ).val = τ.val ∘ identifyVertex Z) ∧
    (Colorable q (identify F Z) ↔ ∃ σ, IsColoring q F σ ∧ constantOn σ Z) ∧
    (Colorable q (identify F Z) → Colorable q F)

/-- P3-LOW-04 helper; def:low-identification: cardinality of the actual quotient type. -/
def S5_04AStatement : Prop :=
  ∀ (V : Type) [Fintype V] (Z : Finset V),
    Fintype.card (QuotientVertices Z) = Fintype.card V - Z.card + 1

/-- P3-LOW-04 helper; def:low-identification: an internal occurrence creates a fatal loop. -/
def S5_04BStatement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ) (B : MGraph V) (Z : Finset V),
    ∀ u ∈ Z, ∀ v ∈ Z, 0 < B s(u, v) → ¬ Colorable q (identify B Z)

/-- P3-LOW-05; lem:low-frozen(iv), eq:low-completion: monotonicity and NM. -/
def S5_05Statement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 3 ≤ q →
    (∀ (F F' : MGraph V) (Z : Finset V), Z.Nonempty → subgraph F F' →
      subgraph (identify F Z) (identify F' Z) ∧
      (¬ Colorable q (identify F Z) → ¬ Colorable q (identify F' Z))) ∧
    (∀ (F : MGraph V) (xs : List V), Colorable q F → xs ≠ [] →
      (neverMonochromatic q F xs ↔ ¬ Colorable q (identify F xs.toFinset))) ∧
    (∀ (F : MGraph V) (xs : List V) (Z : Finset V),
      neverMonochromatic q F xs → xs.toFinset ⊆ Z → Z.Nonempty →
      ¬ Colorable q (identify F Z))

/-- P3-LOW-06; eq:low-nm: prefix and uniform-list monotonicity. -/
def S5_06Statement : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (q : ℕ), 3 ≤ q →
  ∀ (B : MGraph V) (d D : ℕ), d ≤ D →
    (∀ xs : List V, xs.length = D →
      neverMonochromatic q B (xs.take d) → neverMonochromatic q B xs) ∧
    0 ≤ nmProbability q d B ∧ nmProbability q d B ≤ nmProbability q D B ∧
    nmProbability q D B ≤ 1 ∧ nmProbability q 0 B = 0

/-- P3-LOW-07; eq:low-quotient: internal edges must be absent. -/
def S5_07Statement : Prop :=
  ∀ (V : Type) [Fintype V] (G : MGraph V), Loopless G →
  ∀ Z : Finset V, Z.Nonempty →
  (∀ u ∈ Z, ∀ v ∈ Z, G s(u, v) = 0) →
  ∀ xs : List {v : V // v ∉ Z},
    (∀ v : {v : V // v ∉ Z}, xs.count v = ∑ a ∈ Z, G s(a, v.val)) →
    identify G Z = addRoot (fun e => G (Sym2.map Subtype.val e)) xs

end ThLean.BP.S5
