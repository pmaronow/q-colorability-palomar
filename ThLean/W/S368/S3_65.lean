import ThLean.BP.S3.Cycles
import ThLean.Contrib.S368.BadComponent

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u

namespace ThLean.W.S368
open ThresholdFoundations ThLean.BP.S3 ThLean.Contrib.S368

/-- S3-65 from the seven neighboring structural leaves and the component
extraction/transport statement recorded in `HasBadConnectedComponent`. -/
theorem S3_65Statement_from_deps_and_component
    (h55 : S3_55Statement.{u})
    (h56 : S3_56Statement.{u})
    (h57a : S3_57aStatement.{u})
    (h63a : S3_63aStatement.{u})
    (h63b : S3_63bStatement.{u})
    (h66 : S3_66Statement.{u})
    (h67 : S3_67Statement.{u})
    (hcomponent : ∀ (V : Type u) [Fintype V] (q : ℕ), 3 ≤ q →
      2 ≤ Fintype.card V → ∀ G : MGraph V, Loopless G → ¬ Colorable q G →
        HasBadConnectedComponent q G) :
    S3_65Statement.{u} := by
  intro V _ q hq hV G hG hnotColorable
  obtain ⟨S, H, lift, hWtwo, hWle, hHloopless, hHconnected, hHnotColorable,
    hLiftSubgraph, hLiftLoopless, hLiftEdgeCount, hLiftVertexCount,
    hLiftTheta, hLiftDumbbell⟩ :=
      hcomponent V q hq hV G hG hnotColorable
  let W := {v : V // v ∈ S}
  have h57 := S3_57_assembly h55 h56 h57a
  have hTooMany : Fintype.card W < edgeCount H := by
    by_contra h
    apply hHnotColorable
    exact h57 W q hq hWtwo H hHloopless hHconnected (Nat.le_of_not_gt h)
  have hEdgeThreshold : Fintype.card W + 1 ≤ edgeCount H := by omega
  have finish : ∀ (F : MGraph W), subgraph F H → Loopless F →
      (ExactTheta F ∨ ExactDumbbell F) →
      ∃ k : ℕ, ∃ F' : MGraph V, 2 ≤ k ∧ k ≤ Fintype.card V ∧
        subgraph F' G ∧ Witness k F' ∧ edgeCount F' = k + 1 := by
    intro F hFsub hFloopless hFshape
    rcases hFshape with hFtheta | hFdumbbell
    · let k := (vertexSupport F).card
      obtain ⟨hk, hFedges, _⟩ := (h66 W).1 F hFtheta
      have hWitness : Witness k (lift F) := by
        refine ⟨hLiftLoopless F hFloopless, ?_, Or.inl (hLiftTheta F hFtheta)⟩
        simpa [k] using hLiftVertexCount F
      have hBound : k ≤ Fintype.card V := by
        calc
          k ≤ Fintype.card W := by
            dsimp [k]
            exact Finset.card_le_univ _
          _ ≤ Fintype.card V := hWle
      refine ⟨k, lift F, ?_, hBound, hLiftSubgraph F hFsub, hWitness, ?_⟩
      · simpa [k] using hk
      · calc
          edgeCount (lift F) = edgeCount F := hLiftEdgeCount F
          _ = k + 1 := by simpa [k] using hFedges
    · let k := (vertexSupport F).card
      obtain ⟨hk, hFedges, _⟩ := (h67 W).1 F hFdumbbell
      have hWitness : Witness k (lift F) := by
        refine ⟨hLiftLoopless F hFloopless, ?_, Or.inr (hLiftDumbbell F hFdumbbell)⟩
        simpa [k] using hLiftVertexCount F
      have hBound : k ≤ Fintype.card V := by
        calc
          k ≤ Fintype.card W := by
            dsimp [k]
            exact Finset.card_le_univ _
          _ ≤ Fintype.card V := hWle
      refine ⟨k, lift F, ?_, hBound, hLiftSubgraph F hFsub, hWitness, ?_⟩
      · simpa [k] using hk
      · calc
          edgeCount (lift F) = edgeCount F := hLiftEdgeCount F
          _ = k + 1 := by simpa [k] using hFedges
  rcases h63a W hWtwo H hHloopless hHconnected hEdgeThreshold with hTheta | hDumbbell
  · obtain ⟨F, hFsub, hFloopless, hFshape⟩ :=
      h63b W H hHloopless (Or.inl hTheta)
    exact finish F hFsub hFloopless hFshape
  · obtain ⟨F, hFsub, hFloopless, hFshape⟩ :=
      h63b W H hHloopless (Or.inr hDumbbell)
    exact finish F hFsub hFloopless hFshape

end ThLean.W.S368
