import ThLean.BP.SA.Interpolation
import ThLean.Contrib.SA39.MixedPoissonSupport

noncomputable section
open scoped BigOperators

namespace ThLean.W.SA39
open ThresholdFoundations
open ThLean.BP.SA

theorem SA_I16dStatement_of_deps
    (h10 : SA_I10Statement)
    (hmark : ThLean.Contrib.SA39.MixedMarkSupportStatement) :
    SA_I16dStatement := by
  intro q n₁ n₂ hq hn₁ hn₂ c hc θ hθ
  have hcolorings := (h10 (Fin (n₁ + n₂)) q hq).1
  have hsupportInvariant : ∀ G G' : MGraph (Fin (n₁ + n₂)),
      edgeSupport G = edgeSupport G' →
        interpolationClassDrift q n₁ n₂ G = interpolationClassDrift q n₁ n₂ G' := by
    intro G G' hG
    have hcs : colorings q G = colorings q G' := hcolorings G G' hG
    have hIs : ∀ σ, IsColoring q G σ ↔ IsColoring q G' σ := by
      intro σ
      have hm : σ ∈ colorings q G ↔ σ ∈ colorings q G' := by rw [hcs]
      simpa [colorings] using hm
    have hC : Colorable q G ↔ Colorable q G' := by
      constructor
      · rintro ⟨σ, hs⟩
        exact ⟨σ, (hIs σ).mp hs⟩
      · rintro ⟨σ, hs⟩
        exact ⟨σ, (hIs σ).mpr hs⟩
    have hF : Frozen q G = Frozen q G' := by
      funext u v
      apply propext
      change (Colorable q G ∧ ∀ σ, IsColoring q G σ → σ u = σ v) ↔
        (Colorable q G' ∧ ∀ σ, IsColoring q G' σ → σ u = σ v)
      constructor
      · rintro ⟨hc, hσ⟩
        exact ⟨hC.mp hc, fun σ hs => hσ σ ((hIs σ).mpr hs)⟩
      · rintro ⟨hc, hσ⟩
        exact ⟨hC.mpr hc, fun σ hs => hσ σ ((hIs σ).mp hs)⟩
    have hfc : ∀ u, frozenClass q G u = frozenClass q G' u := by
      intro u
      unfold frozenClass
      rw [hF]
    have hclasses : frozenClasses q G = frozenClasses q G' := by
      unfold frozenClasses
      ext C
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
        true_and]
      constructor
      · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
        exact ⟨⟨u, (hfc u).symm.trans hu⟩, ⟨v, hv⟩⟩
      · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
        exact ⟨⟨u, (hfc u).trans hu⟩, ⟨v, hv⟩⟩
    simp only [interpolationClassDrift, hclasses]
  have hmeans := hmark n₁ n₂ (interpolationMeans n₁ n₂ c θ)
      (interpolationClassDrift q n₁ n₂) hsupportInvariant
  refine ⟨hmeans.1, ?_⟩
  simpa [driftMean, drift, supportMean, ThLean.BP.SA.supportGraph] using hmeans.2

end ThLean.W.SA39
