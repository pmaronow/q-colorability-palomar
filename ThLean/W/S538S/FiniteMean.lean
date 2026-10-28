import ThLean.BP.S5.Main

/-!
The finite-average helpers `uniformMean_nonneg`
match implementation patterns in OpenAI's math library (Apache-2.0).
Local versions use project-specific averaging definitions and namespaces.
Their source credits and licence scope are listed in NOTICE; the licence
text is in LICENSES/Apache-2.0.txt.
-/

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S538S
open ThresholdFoundations

lemma uniformMean_nonneg {A : Type*} [Fintype A] (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a) : 0 ≤ uniformMean f := by
  exact div_nonneg (Finset.sum_nonneg fun a _ => hf a) (Nat.cast_nonneg _)

lemma uniformMeanENN_mono {A : Type*} [Fintype A] {f g : A → ℝ≥0∞}
    (hfg : ∀ a, f a ≤ g a) : uniformMeanENN f ≤ uniformMeanENN g := by
  exact ENNReal.div_le_div_right (Finset.sum_le_sum fun a _ => hfg a) _

lemma uniformMeanENN_ofReal {A : Type*} [Fintype A] (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a) :
    uniformMeanENN (fun a => ENNReal.ofReal (f a)) = ENNReal.ofReal (uniformMean f) := by
  by_cases hA : Nonempty A
  · have hc : 0 < (Fintype.card A : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr hA
    simp [uniformMeanENN, uniformMean, ENNReal.ofReal_div_of_pos hc,
      ENNReal.ofReal_sum_of_nonneg (fun a _ => hf a)]
  · have : IsEmpty A := not_nonempty_iff.mp hA
    simp [uniformMeanENN, uniformMean]

lemma terminalStepENN_ofReal {V : Type*} [Fintype V] (q m : ℕ)
    (h : MGraph V → Pair V → ℝ) (hh : ∀ G e, 0 ≤ h G e) :
    terminalStepENN q m (fun G e => ENNReal.ofReal (h G e)) =
      ENNReal.ofReal (terminalStep q m h) := by
  have hinner (G : MGraph V) :
      uniformMeanENN (fun e : Pair V =>
        if Colorable q G ∧ ¬ Colorable q (addPair G e)
        then ENNReal.ofReal (h G e) else 0) =
      ENNReal.ofReal (uniformMean (fun e : Pair V =>
        if Colorable q G ∧ ¬ Colorable q (addPair G e) then h G e else 0)) := by
    convert uniformMeanENN_ofReal
      (fun e : Pair V => if Colorable q G ∧ ¬ Colorable q (addPair G e)
        then h G e else 0)
      (fun e => by split_ifs <;> first | exact hh _ _ | exact le_rfl) using 1
    congr 1
    funext e
    split_ifs <;> simp
  unfold terminalStepENN terminalStep
  simp_rw [hinner]
  apply uniformMeanENN_ofReal
  intro x
  apply uniformMean_nonneg
  intro e
  split_ifs <;> first | exact hh _ _ | exact le_rfl

lemma ofReal_indicator (P : Prop) :
    ENNReal.ofReal (indicator P) = if P then 1 else 0 := by
  by_cases hP : P <;> simp [indicator, hP]

end ThLean.W.S538S
