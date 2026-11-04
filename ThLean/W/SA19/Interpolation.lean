module

public import ThLean.BP.SA.Interpolation

@[expose] public section

noncomputable section

namespace ThLean.W.SA19

open ThresholdFoundations

theorem SA_I10Statement_holds : ThLean.BP.SA.SA_I10Statement := by
  intro V _ q hq
  refine ⟨?_, ?_, ?_⟩
  · intro G G' hsupport
    have hpos : ∀ e : Sym2 V, 0 < G e ↔ 0 < G' e := by
      intro e
      have hm := congrArg (fun S : Finset (Sym2 V) => e ∈ S) hsupport
      simpa [edgeSupport] using hm
    apply Finset.ext
    intro σ
    simp only [colorings, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h u v huv
      exact h u v ((hpos s(u, v)).mpr huv)
    · intro h u v huv
      exact h u v ((hpos s(u, v)).mp huv)
  · intro G v hloop hcolor
    rcases hcolor with ⟨σ, hσ⟩
    exact (hσ v v hloop) rfl
  · intro G x y σ
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro u v huv
        have hadded : 0 < addEdge G s(x, y) s(u, v) := by
          by_cases he : s(u, v) = s(x, y)
          · simp [addEdge, he]
          · simp [addEdge, he, huv]
        exact h u v hadded
      · exact h x y (by simp [addEdge])
    · rintro ⟨hG, hxy⟩ u v huv
      by_cases he : s(u, v) = s(x, y)
      · have hendpoints : u = x ∧ v = y ∨ u = y ∧ v = x :=
          Sym2.eq_iff.mp he
        rcases hendpoints with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hxy
        · exact hxy.symm
      · have hold : 0 < G (s(u, v)) := by
          simpa [addEdge, he] using huv
        exact hG u v hold

example : ThLean.BP.SA.SA_I10Statement := SA_I10Statement_holds

end ThLean.W.SA19
