module

public import ThLean.W.S541S.RootGraph

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S541S
open ThresholdFoundations ThLean.BP.S5

theorem nmProbability_bounds {V : Type*} [Fintype V] [Nonempty V]
    (q j : ℕ) (B : MGraph V) :
    0 ≤ nmProbability q j B ∧ nmProbability q j B ≤ 1 :=
  uniformMean_bounds fun _ => indicator_bounds _

theorem listMean_root_bounds {V : Type*} [Fintype V] [Nonempty V]
    (q D j : ℕ) (B : MGraph V) :
    0 ≤ listMean j (fun xs => indicator (rootEvent q D none (addRoot B xs))) ∧
      listMean j (fun xs => indicator (rootEvent q D none (addRoot B xs))) ≤ 1 :=
  uniformMean_bounds fun _ => indicator_bounds _

theorem listMean_root_le {V : Type} [Fintype V] [Nonempty V]
    (q D j : ℕ) (hq : 3 ≤ q) (B : MGraph V) :
    listMean j (fun xs => indicator (rootEvent q D none (addRoot B xs))) ≤
      if j ≤ D then nmProbability q j B else 0 := by
  by_cases hj : j ≤ D
  · rw [ite_eq_left hj]
    apply uniformMean_mono
    intro x
    apply indicator_mono
    intro hx
    exact (rootEvent_addRoot_imp q D hq B _ hx).2
  · rw [ite_eq_right hj]
    have hzero : (fun x : Fin j → V =>
        indicator (rootEvent q D none (addRoot B (List.ofFn x)))) = fun _ => 0 := by
      funext x
      apply ite_eq_right
      intro hx
      have hxj := (rootEvent_addRoot_imp q D hq B _ hx).1
      simp only [List.length_ofFn] at hxj
      exact hj hxj
    change uniformMean _ ≤ 0
    rw [hzero, uniformMean_const]

theorem truncated_nm_bounds {V : Type} [Fintype V] [Nonempty V]
    (hE01 : S5_E01Statement) {z : ℝ} (hz : 0 ≤ z) (q D : ℕ) (B : MGraph V) :
    0 ≤ (∑ j ∈ Finset.range (D + 1), poissonWeight z j * nmProbability q j B) ∧
      (∑ j ∈ Finset.range (D + 1), poissonWeight z j * nmProbability q j B) ≤ 1 := by
  rw [← poissonMixture_truncate z]
  apply (poissonMixture_bounds hE01 hz _).2
  intro j
  split_ifs
  · exact nmProbability_bounds q j B
  · exact ⟨le_rfl, zero_le_one⟩

theorem root_mixture_le {V : Type} [Fintype V] [Nonempty V]
    (hE01 : S5_E01Statement) {z : ℝ} (hz : 0 ≤ z)
    (q D : ℕ) (hq : 3 ≤ q) (B : MGraph V) :
    poissonMixture z (fun j =>
      listMean j (fun xs => indicator (rootEvent q D none (addRoot B xs)))) ≤
        ∑ j ∈ Finset.range (D + 1), poissonWeight z j * nmProbability q j B := by
  rw [← poissonMixture_truncate z]
  apply poissonMixture_mono hE01 hz (fun j => listMean_root_bounds q D j B)
  · intro j
    split_ifs
    · exact nmProbability_bounds q j B
    · exact ⟨le_rfl, zero_le_one⟩
  · intro j
    exact listMean_root_le q D j hq B

theorem rootProbability_option_le {V : Type} [Fintype V] [Nonempty V]
    [Nonempty (Pair V)] (h09B : S5_09BStatement) (hE01 : S5_E01Statement)
    (hV : 2 ≤ Fintype.card V) (q D : ℕ) (hq : 3 ≤ q) (t : ℝ) (ht : 0 ≤ t) :
    rootProbability (V := Option V) q D none t ≤
      ∑ j ∈ Finset.range (D + 1),
        poissonWeight (2 * t / ((Fintype.card V : ℝ) + 1)) j *
          poissonGraphMean ((((Fintype.card V : ℝ) - 1) /
            ((Fintype.card V : ℝ) + 1)) * t) (nmProbability (V := V) q j) := by
  have hcard : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hV
  have hz : 0 ≤ 2 * t / ((Fintype.card V : ℝ) + 1) := by positivity
  have hs : 0 ≤ (((Fintype.card V : ℝ) - 1) /
      ((Fintype.card V : ℝ) + 1)) * t :=
    mul_nonneg (div_nonneg (by linarith) (by positivity)) ht
  unfold rootProbability
  rw [h09B V hV t ht _ ⟨1, fun G => by
    rw [abs_of_nonneg (indicator_bounds _).1]
    exact (indicator_bounds _).2⟩]
  calc
    _ ≤ poissonGraphMean ((((Fintype.card V : ℝ) - 1) /
        ((Fintype.card V : ℝ) + 1)) * t)
        (fun B : MGraph V => ∑ j ∈ Finset.range (D + 1),
          poissonWeight (2 * t / ((Fintype.card V : ℝ) + 1)) j *
            nmProbability q j B) := by
      apply poissonGraphMean_mono hE01 hs
      · intro B
        exact (poissonMixture_bounds hE01 hz fun j => listMean_root_bounds q D j B).2
      · intro B
        exact truncated_nm_bounds hE01 hz q D B
      · intro B
        exact root_mixture_le hE01 hz q D hq B
    _ = _ := poissonGraphMean_finset_sum hE01 hs _ _ _
      (fun j B => nmProbability_bounds q j B)

theorem truncated_nmTime_le (h06 : S5_06Statement) (hE01 : S5_E01Statement)
    (q N D : ℕ) (hq : 3 ≤ q) (hN : 2 ≤ N) {z s : ℝ}
    (hz : 0 ≤ z) (hs : 0 ≤ s) :
    (∑ j ∈ Finset.range (D + 1), poissonWeight z j * nmTime q N j s) ≤
      nmTime q N D s := by
  have : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have : Nonempty (Pair (Fin N)) := by
    let u : Fin N := ⟨0, by omega⟩
    let v : Fin N := ⟨1, by omega⟩
    refine ⟨⟨s(u, v), ?_⟩⟩
    intro w he
    have h := Sym2.eq_iff.mp he
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> have := h1.trans h2.symm <;>
      simp [u, v, Fin.ext_iff] at this
  have hnonneg : 0 ≤ nmTime q N D s :=
    (poissonGraphMean_bounds hE01 hs (nmProbability_bounds q D)).1
  have hmono (j : ℕ) (hj : j ≤ D) : nmTime q N j s ≤ nmTime q N D s := by
    apply poissonGraphMean_mono hE01 hs (nmProbability_bounds q j)
      (nmProbability_bounds q D)
    intro B
    exact (h06 (Fin N) q hq B j D hj).2.2.1
  calc
    _ ≤ ∑ j ∈ Finset.range (D + 1), poissonWeight z j * nmTime q N D s := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hmono j (by have := Finset.mem_range.mp hj; omega))
        ((hE01.1 z hz).1 j).1
    _ = (∑ j ∈ Finset.range (D + 1), poissonWeight z j) * nmTime q N D s :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * nmTime q N D s :=
      mul_le_mul_of_nonneg_right (poisson_partial_mass_le_one hE01 hz D) hnonneg
    _ = _ := one_mul _

end ThLean.W.S541S
