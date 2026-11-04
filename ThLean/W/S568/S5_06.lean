module

public import ThLean.BP.S5.Structure

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S568

open ThresholdFoundations

private theorem uniformMean_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) : uniformMean (f ∘ e) = uniformMean f := by
  unfold uniformMean
  change (∑ a, f (e a)) / (Fintype.card A : ℝ) = _
  rw [Equiv.sum_comp e f, Fintype.card_congr e]

private theorem uniformMean_mono {A : Type*} [Fintype A] [Nonempty A]
    {f g : A → ℝ} (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  unfold uniformMean
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < (Fintype.card A : ℝ))).2
  exact Finset.sum_le_sum fun a _ => h a

private theorem uniformMean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    uniformMean (fun _ : A => c) = c := by
  unfold uniformMean
  simp [Fintype.card_ne_zero]

private theorem uniformMean_prod {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (f : A × B → ℝ) :
    uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a, b))) := by
  unfold uniformMean
  rw [Fintype.sum_prod_type]
  rw [Fintype.card_prod]
  have hsum :
      (∑ a : A, (∑ b : B, f (a, b)) / (Fintype.card B : ℝ)) =
        (∑ a : A, ∑ b : B, f (a, b)) / (Fintype.card B : ℝ) := by
    rw [← Finset.sum_div]
  rw [hsum, div_div]
  congr 1
  simp [Nat.cast_mul, mul_comm]

private theorem uniformProb_nonneg {A : Type*} [Fintype A] [Nonempty A]
    (P : A → Prop) : 0 ≤ uniformProb P := by
  unfold uniformProb uniformMean
  apply div_nonneg
  · exact Finset.sum_nonneg fun a _ => by
      by_cases h : P a <;> simp [indicator, h]
  · positivity

private theorem uniformProb_le_one {A : Type*} [Fintype A] [Nonempty A]
    (P : A → Prop) : uniformProb P ≤ 1 := by
  unfold uniformProb uniformMean
  apply (div_le_one₀ (by positivity : 0 < (Fintype.card A : ℝ))).2
  calc
    (∑ a, indicator (P a)) ≤ ∑ _a : A, (1 : ℝ) :=
      Finset.sum_le_sum fun a _ => by by_cases h : P a <;> simp [indicator, h]
    _ = (Fintype.card A : ℝ) := by simp

private theorem neverMonochromatic_append {V : Type*} [Fintype V]
    (q : ℕ) (B : MGraph V) {xs ys : List V}
    (h : neverMonochromatic q B xs) : neverMonochromatic q B (xs ++ ys) := by
  rcases h with ⟨hcolor, hnm⟩
  refine ⟨hcolor, fun σ hσ => ?_⟩
  have himage : (xs.map σ).toFinset ⊆ ((xs ++ ys).map σ).toFinset := by
    intro c hc
    change c ∈ (xs.map σ).toFinset at hc
    simp only [List.mem_toFinset, List.mem_map] at hc ⊢
    rcases hc with ⟨v, hv, rfl⟩
    exact ⟨v, List.mem_append_left _ hv, rfl⟩
  exact le_trans (hnm σ hσ) (Finset.card_le_card himage)

private theorem neverMonochromatic_snoc_implies {V : Type*} [Fintype V]
    (q : ℕ) (B : MGraph V) (m : ℕ) (p : Fin m → V) (v : V)
    (h : neverMonochromatic q B (List.ofFn p)) :
    neverMonochromatic q B (List.ofFn (Fin.snoc p v)) := by
  have hlist : List.ofFn (Fin.snoc p v) = List.ofFn p ++ [v] := by
    rw [List.ofFn_succ']
    simp
  rw [hlist]
  exact neverMonochromatic_append q B h

private theorem nmProbability_step {V : Type*} [Fintype V] [Nonempty V]
    (q : ℕ) (B : MGraph V) (m : ℕ) :
    nmProbability q m B ≤ nmProbability q (m + 1) B := by
  let e : (Fin m → V) × V ≃ (Fin (m + 1) → V) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ : Fin (m + 1) => V))
  have hreindex :
      uniformMean (fun z : (Fin m → V) × V =>
        indicator (neverMonochromatic q B (List.ofFn (e z)))) =
      uniformMean (fun x : Fin (m + 1) → V =>
        indicator (neverMonochromatic q B (List.ofFn x))) := by
    exact uniformMean_equiv e (fun x => indicator (neverMonochromatic q B (List.ofFn x)))
  have hpoint : ∀ z : (Fin m → V) × V,
      indicator (neverMonochromatic q B (List.ofFn z.1)) ≤
        indicator (neverMonochromatic q B (List.ofFn (e z))) := by
    intro z
    change indicator (neverMonochromatic q B (List.ofFn z.1)) ≤
      indicator (neverMonochromatic q B (List.ofFn (Fin.snoc z.1 z.2)))
    by_cases hp : neverMonochromatic q B (List.ofFn z.1)
    · have hext := neverMonochromatic_snoc_implies q B m z.1 z.2 hp
      simp only [indicator, if_pos hp, if_pos hext]
      norm_num
    · simp only [indicator, if_neg hp]
      split_ifs <;> norm_num
  have hprod :
      uniformMean (fun z : (Fin m → V) × V =>
        indicator (neverMonochromatic q B (List.ofFn (e z)))) =
      uniformMean (fun p : Fin m → V =>
        uniformMean (fun v : V =>
          indicator (neverMonochromatic q B (List.ofFn (Fin.snoc p v))))) := by
    rw [uniformMean_prod]
    rfl
  have hprefix :
      uniformMean (fun p : Fin m → V =>
        indicator (neverMonochromatic q B (List.ofFn p))) ≤
      uniformMean (fun z : (Fin m → V) × V =>
        indicator (neverMonochromatic q B (List.ofFn (e z)))) := by
    calc
      uniformMean (fun p : Fin m → V =>
          indicator (neverMonochromatic q B (List.ofFn p))) =
        uniformMean (fun p : Fin m → V =>
          uniformMean (fun _v : V =>
            indicator (neverMonochromatic q B (List.ofFn p)))) := by
              congr 1
              funext p
              exact (uniformMean_const _).symm
      _ ≤ uniformMean (fun p : Fin m → V =>
          uniformMean (fun v : V =>
            indicator (neverMonochromatic q B (List.ofFn (Fin.snoc p v))))) := by
              apply uniformMean_mono
              intro p
              apply uniformMean_mono
              intro v
              exact hpoint (p, v)
      _ = uniformMean (fun z : (Fin m → V) × V =>
          indicator (neverMonochromatic q B (List.ofFn (e z)))) := hprod.symm
  simpa [nmProbability, uniformProb] using hprefix.trans_eq hreindex

private theorem nmProbability_mono {V : Type*} [Fintype V] [Nonempty V]
    (q : ℕ) (B : MGraph V) {d D : ℕ} (h : d ≤ D) :
    nmProbability q d B ≤ nmProbability q D B := by
  have haux : ∀ k, nmProbability q d B ≤ nmProbability q (d + k) B := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          nmProbability q d B ≤ nmProbability q (d + k) B := ih
          _ ≤ nmProbability q (d + k + 1) B := by
            simpa [Nat.add_assoc] using nmProbability_step q B (d + k)
          _ = nmProbability q (d + (k + 1)) B := by rw [Nat.add_assoc]
  have hEq : d + (D - d) = D := Nat.add_sub_of_le h
  calc
    nmProbability q d B ≤ nmProbability q (d + (D - d)) B := haux (D - d)
    _ = nmProbability q D B := by rw [hEq]

theorem S5_06Statement_holds : ThLean.BP.S5.S5_06Statement := by
  intro V _ _ q hq B d D hdD
  refine ⟨?_, ?_⟩
  · intro xs hlen hprefix
    have h := neverMonochromatic_append q B (ys := xs.drop d) hprefix
    simpa [List.take_append_drop] using h
  · refine ⟨uniformProb_nonneg _, ?_⟩
    refine ⟨nmProbability_mono q B hdD, ?_⟩
    refine ⟨uniformProb_le_one _, ?_⟩
    have hempty : ¬ neverMonochromatic q B ([] : List V) := by
      rintro ⟨hc, hnm⟩
      rcases hc with ⟨σ, hσ⟩
      have := hnm σ hσ
      simp at this
    unfold nmProbability uniformProb uniformMean
    simp [hempty, indicator]

example : ThLean.BP.S5.S5_06Statement := S5_06Statement_holds

end ThLean.W.S568
