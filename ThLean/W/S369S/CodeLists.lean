module

public import ThLean.W.S369S.TripleLists

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S369S
open ThresholdFoundations ThLean.BP.S3
variable {V : Type u} [Fintype V]

theorem range_blocks (f : ℕ → V) (m n r : ℕ) :
    thetaLabels (f 0) (f 1)
      ((List.range m).map (fun i => f (2+i)))
      ((List.range n).map (fun i => f (2+m+i)))
      ((List.range r).map (fun i => f (2+m+n+i))) =
      (List.range (2+m+n+r)).map f := by
  simp only [List.range_add, List.map_append, List.map_map, Function.comp_def]
  rfl

theorem range_codeLabel {k : ℕ} (hk : 0 < k) (v : Fin k → V) :
    (List.range k).map (codeLabel hk v) = List.ofFn v := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn,
      codeLabel, Nat.mod_eq_of_lt hi]

theorem code_labels {k : ℕ} (hk : 0 < k) (j₁ j₂ j₃ : ℕ) (v : Fin k → V)
    (h₁ : 1 ≤ j₁) (h₂ : 1 ≤ j₂) (h₃ : 1 ≤ j₃) (hs : j₁+j₂+j₃=k+1) :
    thetaLabels (codeLabel hk v 0) (codeLabel hk v 1)
      ((List.range (j₁-1)).map (fun i => codeLabel hk v (2+i)))
      ((List.range (j₂-1)).map (fun i => codeLabel hk v (j₁+1+i)))
      ((List.range (j₃-1)).map (fun i => codeLabel hk v (j₁+j₂+i))) = List.ofFn v := by
  have e₁ : 2+(j₁-1) = j₁+1 := by omega
  have e₂ : 2+(j₁-1)+(j₂-1) = j₁+j₂ := by omega
  have e₃ : 2+(j₁-1)+(j₂-1)+(j₃-1) = k := by omega
  have h := range_blocks (codeLabel hk v) (j₁-1) (j₂-1) (j₃-1)
  rw [e₃, e₂, e₁, range_codeLabel] at h
  exact h

theorem thetaCode_exact_support {k : ℕ} (hk : 0 < k) (j₁ j₂ j₃ : ℕ) (v : Fin k ↪ V)
    (h₁ : 1 ≤ j₁) (h₂ : 1 ≤ j₂) (h₃ : 1 ≤ j₃) (hs : j₁+j₂+j₃=k+1) :
    ExactTheta (thetaCode hk j₁ j₂ j₃ v) ∧
      (vertexSupport (thetaCode hk j₁ j₂ j₃ v)).card = k := by
  have hn : (List.ofFn v).Nodup := List.nodup_ofFn.mpr v.injective
  have hl := code_labels hk j₁ j₂ j₃ v h₁ h₂ h₃ hs
  constructor
  · apply thetaLists_exact
    rw [hl]
    exact hn
  · change (vertexSupport (thetaLists (codeLabel hk v 0) (codeLabel hk v 1)
      ((List.range (j₁-1)).map (fun i => codeLabel hk v (2+i)))
      ((List.range (j₂-1)).map (fun i => codeLabel hk v (j₁+1+i)))
      ((List.range (j₃-1)).map (fun i => codeLabel hk v (j₁+j₂+i))))).card = k
    rw [support_thetaLists, hl, List.toFinset_card_of_nodup hn, List.length_ofFn]

/-- Reading the concatenated labels recovers the three original lists. -/
theorem thetaCode_get_labels (a b : V) (x y z : List V)
    (hk : 0 < (thetaLabels a b x y z).length) :
    thetaCode hk (x.length+1) (y.length+1) (z.length+1)
      (thetaLabels a b x y z).get = thetaLists a b x y z := by
  have hs : (x.length+1)+(y.length+1)+(z.length+1) =
      (thetaLabels a b x y z).length+1 := by simp [thetaLabels]; omega
  have hl := code_labels hk (x.length+1) (y.length+1) (z.length+1)
    (thetaLabels a b x y z).get (by omega) (by omega) (by omega) hs
  rw [List.ofFn_get] at hl
  unfold thetaLabels at hl
  have hZ := List.append_inj' hl (by simp)
  have hY := List.append_inj' hZ.1 (by simp)
  have hX := List.append_inj' hY.1 (by simp)
  have ha := (List.cons.inj hX.1).1
  have hb := (List.cons.inj (List.cons.inj hX.1).2).1
  dsimp only [thetaCode, thetaLabels]
  rw [ha, hb, hX.2, hY.2, hZ.2]
  rfl

end ThLean.W.S369S
