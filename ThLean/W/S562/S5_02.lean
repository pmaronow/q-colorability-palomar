import ThLean.BP.S5.Structure

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S562

open ThresholdFoundations

theorem S5_02Statement_of_deps
    (h01A : ThLean.BP.S5.S5_01AStatement) :
    ThLean.BP.S5.S5_02Statement := by
  intro V _ q hq B hB xs b hcolor
  let G : MGraph (Option V) := addRoot B xs
  have happend : Colorable q (addRoot B (xs ++ [b])) ↔
      ∃ τ, IsColoring q G τ ∧ τ none ≠ τ (some b) := by
    constructor
    · rintro ⟨τ, hτ⟩
      have hτ' := h01A V q hq B (xs ++ [b]) τ
      have hbase : IsColoring q B (fun v => τ (some v)) := (hτ'.mp hτ).1
      have hlist : ∀ v ∈ xs ++ [b], τ none ≠ τ (some v) := (hτ'.mp hτ).2
      refine ⟨τ, ?_, hlist b (by simp)⟩
      exact (h01A V q hq B xs τ).mpr ⟨hbase, fun v hv => hlist v (by simp [hv])⟩
    · rintro ⟨τ, hτ, hneq⟩
      have hbase : IsColoring q B (fun v => τ (some v)) :=
        ((h01A V q hq B xs τ).mp hτ).1
      have hτext : IsColoring q (addRoot B (xs ++ [b])) τ := by
        apply (h01A V q hq B (xs ++ [b]) τ).mpr
        refine ⟨hbase, fun v hv => ?_⟩
        rcases List.mem_append.mp hv with hv | hv
        · exact ((h01A V q hq B xs τ).mp hτ).2 v hv
        · simp at hv
          subst v
          exact hneq
      exact ⟨τ, hτext⟩
  change (Colorable q G ∧ (∀ τ, IsColoring q G τ → τ none = τ (some b))) ↔
    ¬ Colorable q (addRoot B (xs ++ [b]))
  rw [happend]
  constructor
  · rintro ⟨_, heq⟩ ⟨τ, hτ, hneq⟩
    exact hneq (heq τ hτ)
  · intro hnot
    refine ⟨hcolor, ?_⟩
    intro τ hτ
    by_contra hneq
    exact hnot ⟨τ, hτ, hneq⟩

end ThLean.W.S562
