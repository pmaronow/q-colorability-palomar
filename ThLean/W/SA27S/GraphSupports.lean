import ThLean.W.SA27S.TripleWeights

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA27S
open ThresholdFoundations ThLean.BP.SA

def taggedCountsEquiv (A B C : Type) :
    (A ⊕ (B ⊕ C) → ℕ) ≃ TripleCounts A B C :=
  (Equiv.sumArrowEquivProdArrow A (B ⊕ C) ℕ).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.sumArrowEquivProdArrow B C ℕ))

lemma histogram_pos {D : Type} [DecidableEq D] (p : Prefix D) (d : D) :
    0 < histogram p d ↔ ∃ i, p.2 i = d := by
  simp [histogram, List.count_pos_iff, List.mem_ofFn]

lemma orderedTupleGraph_pos {V : Type} [Fintype V] {k : ℕ}
    (x : Fin k → V × V) (e : Sym2 V) :
    0 < orderedTupleGraph x e ↔ ∃ i, s((x i).1, (x i).2) = e := by
  simp [orderedTupleGraph, Finset.card_pos, Finset.Nonempty]

lemma map_orderedTupleGraph_pos {V W : Type} [Fintype V] [Fintype W]
    (f : V → W) {k : ℕ} (x : Fin k → V × V) (e : Sym2 W) :
    0 < mapGraph f (orderedTupleGraph x) e ↔
      ∃ i, s(f (x i).1, f (x i).2) = e := by
  simp only [mapGraph, Finset.sum_pos_iff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha⟩
    split_ifs at ha with h
    · obtain ⟨i, hi⟩ := (orderedTupleGraph_pos x a).mp ha
      exact ⟨i, by simpa [← hi] using h⟩
    · omega
  · rintro ⟨i, hi⟩
    refine ⟨s((x i).1, (x i).2), ?_⟩
    have he : Sym2.map f s((x i).1, (x i).2) = e := by simpa using hi
    rw [ite_eq_left he]
    exact (orderedTupleGraph_pos x _).mpr ⟨i, rfl⟩

lemma supportGraph_pos {D V : Type} [Fintype D] (edge : D → Sym2 V)
    (z : D → ℕ) (e : Sym2 V) :
    0 < ThresholdFoundations.supportGraph edge (Finset.univ.filter (fun d => 0 < z d)) e ↔
      ∃ d, 0 < z d ∧ edge d = e := by
  simp [ThresholdFoundations.supportGraph, Finset.card_pos, Finset.Nonempty]

abbrev Endpoints (n : ℕ) := Fin n × Fin n
abbrev InterpolationPrefix (n₁ n₂ : ℕ) :=
  TriplePrefix (Endpoints (n₁ + n₂)) (Endpoints n₁) (Endpoints n₂)

def prefixMixedGraph {n₁ n₂ : ℕ} (p : InterpolationPrefix n₁ n₂) :
    MGraph (Fin (n₁ + n₂)) := mixedGraph p.1.2 p.2.1.2 p.2.2.2

def interpolationHistogram {n₁ n₂ : ℕ} (p : InterpolationPrefix n₁ n₂) :
    InterpolationMark n₁ n₂ → ℕ :=
  (taggedCountsEquiv (Endpoints (n₁ + n₂)) (Endpoints n₁) (Endpoints n₂)).symm
    (tripleHistogram p)

@[simp] lemma interpolationHistogram_global {n₁ n₂ : ℕ}
    (p : InterpolationPrefix n₁ n₂) (d : Endpoints (n₁ + n₂)) :
    interpolationHistogram p (.inl d) = histogram p.1 d := rfl

@[simp] lemma interpolationHistogram_left {n₁ n₂ : ℕ}
    (p : InterpolationPrefix n₁ n₂) (d : Endpoints n₁) :
    interpolationHistogram p (.inr (.inl d)) = histogram p.2.1 d := rfl

@[simp] lemma interpolationHistogram_right {n₁ n₂ : ℕ}
    (p : InterpolationPrefix n₁ n₂) (d : Endpoints n₂) :
    interpolationHistogram p (.inr (.inr d)) = histogram p.2.2 d := rfl

lemma mixedGraph_histogram_support (n₁ n₂ : ℕ) (p : InterpolationPrefix n₁ n₂) :
    edgeSupport (prefixMixedGraph p) =
      edgeSupport (ThresholdFoundations.supportGraph interpolationMarkEdge
        (Finset.univ.filter (fun d => 0 < interpolationHistogram p d))) := by
  ext e
  simp only [edgeSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [supportGraph_pos]
  change 0 < (mixedGraph p.1.2 p.2.1.2 p.2.2.2) e ↔ _
  simp only [mixedGraph, Pi.add_apply, Nat.add_pos_iff_pos_or_pos,
    orderedTupleGraph_pos, map_orderedTupleGraph_pos]
  simp only [Sum.exists, interpolationHistogram_global, interpolationHistogram_left,
    interpolationHistogram_right, interpolationMarkEdge, histogram_pos]
  constructor
  · rintro ((⟨i, hi⟩ | ⟨i, hi⟩) | ⟨i, hi⟩)
    · exact Or.inl ⟨p.1.2 i, ⟨i, rfl⟩, hi⟩
    · exact Or.inr (Or.inl ⟨p.2.1.2 i, ⟨i, rfl⟩, hi⟩)
    · exact Or.inr (Or.inr ⟨p.2.2.2 i, ⟨i, rfl⟩, hi⟩)
  · rintro (⟨d, ⟨i, rfl⟩, hi⟩ | ⟨d, ⟨i, rfl⟩, hi⟩ | ⟨d, ⟨i, rfl⟩, hi⟩)
    · exact Or.inl (Or.inl ⟨i, hi⟩)
    · exact Or.inl (Or.inr ⟨i, hi⟩)
    · exact Or.inr ⟨i, hi⟩

lemma colorable_of_edgeSupport_eq (h10 : SA_I10Statement)
    {V : Type} [Fintype V] (q : ℕ) (hq : 1 ≤ q) (G G' : MGraph V)
    (h : edgeSupport G = edgeSupport G') : Colorable q G ↔ Colorable q G' := by
  have he := (h10 V q hq).1 G G' h
  have hnonempty (H : MGraph V) : (colorings q H).Nonempty ↔ Colorable q H := by
    simp [colorings, Colorable, Finset.Nonempty]
  rw [← hnonempty, ← hnonempty, he]

lemma prefixColorable_histogram (h10 : SA_I10Statement)
    (q n₁ n₂ : ℕ) (hq : 1 ≤ q) (p : InterpolationPrefix n₁ n₂) :
    indicator (Colorable q (prefixMixedGraph p)) =
      indicator (Colorable q (ThresholdFoundations.supportGraph interpolationMarkEdge
        (Finset.univ.filter (fun d => 0 < interpolationHistogram p d)))) := by
  congr 1
  exact propext (colorable_of_edgeSupport_eq h10 q hq _ _
    (mixedGraph_histogram_support n₁ n₂ p))

end ThLean.W.SA27S
