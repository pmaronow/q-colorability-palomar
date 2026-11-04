module

public import ThLean.BP.S3.Adapters

@[expose] public section

noncomputable section

open scoped BigOperators ENNReal

universe u

namespace ThLean.W.S385

open ThresholdFoundations

theorem S3_26bStatement_of_deps
    (h26 : ThLean.BP.S3.S3_26Statement.{u}) :
    ThLean.BP.S3.S3_26bStatement.{u} := by
  intro V instV q hq hV G
  have h26all := h26 V q hq hV
  rcases h26all with ⟨_, hgraphs, _, _, _⟩
  rcases hgraphs G with ⟨hfinite, _, _, hbound⟩
  have hsurvival_nonneg : ∀ k : ℕ, 0 ≤ survival q G k := by
    intro k
    simp only [survival, uniformProb, uniformMean]
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro x hx
      simp only [indicator]
      split_ifs <;> norm_num
    · exact Nat.cast_nonneg _
  have hsumENN : (∑' k : ℕ, ENNReal.ofReal (survival q G k)) ≠ ∞ := by
    simpa [lifetime] using hfinite
  have hsum_toReal :
      Summable (fun k : ℕ => (ENNReal.ofReal (survival q G k)).toReal) :=
    ENNReal.summable_toReal hsumENN
  have hterm :
      (fun k : ℕ => (ENNReal.ofReal (survival q G k)).toReal) = survival q G := by
    funext k
    exact ENNReal.toReal_ofReal (hsurvival_nonneg k)
  have hsum_survival : Summable (survival q G) := by
    rw [← hterm]
    exact hsum_toReal
  have htsum_toReal :
      (lifetime q G).toReal =
        ∑' k : ℕ, (ENNReal.ofReal (survival q G k)).toReal := by
    rw [lifetime]
    exact ENNReal.tsum_toReal_eq (fun k => ENNReal.ofReal_ne_top)
  refine ⟨?_, lt_top_iff_ne_top.mpr hfinite, hsum_survival, ?_⟩
  · rw [← ENNReal.ofReal_toReal hfinite]
    exact ENNReal.ofReal_le_ofReal hbound
  · calc
      lifetimeReal q G = (lifetime q G).toReal := rfl
      _ = ∑' k : ℕ, (ENNReal.ofReal (survival q G k)).toReal := htsum_toReal
      _ = ∑' k : ℕ, survival q G k :=
        tsum_congr fun k => ENNReal.toReal_ofReal (hsurvival_nonneg k)

example (h26 : ThLean.BP.S3.S3_26Statement.{u}) :
    ThLean.BP.S3.S3_26bStatement.{u} :=
  S3_26bStatement_of_deps h26

end ThLean.W.S385
