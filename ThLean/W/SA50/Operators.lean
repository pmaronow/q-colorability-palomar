import ThLean.BP.SA.Alternatives

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA50

open ThresholdFoundations ThLean.BP.SA

theorem mean_congr {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a = g a) : uniformMean f = uniformMean g := by
  unfold uniformMean
  congr 1
  exact Finset.sum_congr rfl (fun a _ => h a)

theorem mean_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

theorem mean_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum]
  ring

theorem mean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a))
    (Nat.cast_nonneg _)

theorem mean_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    uniformMean (fun a => uniformMean (f a)) =
      uniformMean (fun b => uniformMean (fun a => f a b)) := by
  simp only [uniformMean, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

theorem mean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformMean (fun _ : α => c) = c := by
  simp [uniformMean, ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos :
    (0 : ℝ) < Fintype.card α)]

theorem mean_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g := by
  simp [uniformMean, Finset.sum_sub_distrib, sub_div]

def edgeMean {V E : Type*} [Fintype E] (edge : E → Sym2 V) :
    (MGraph V → ℝ) → MGraph V → ℝ :=
  fun f G => uniformMean (fun e => f (addEdge G (edge e)))

theorem addEdge_comm {V : Type*} [DecidableEq (Sym2 V)]
    (G : MGraph V) (e d : Sym2 V) :
    addEdge (addEdge G e) d = addEdge (addEdge G d) e := by
  classical
  by_cases h : e = d
  · subst d
    simp [addEdge]
  · ext x
    by_cases hxe : x = e
    · subst x
      simp [addEdge, h]
    · by_cases hxd : x = d
      · subst x
        simp [addEdge, Function.update, hxe]
      · simp [addEdge, hxe, hxd]

theorem edgeMean_mono {V E : Type*} [Fintype E] (edge : E → Sym2 V) :
    Monotone (edgeMean edge) := by
  intro f g h G
  exact mean_mono (fun e => h (addEdge G (edge e)))

theorem edgeMean_commute {V E F : Type*} [Fintype E] [Fintype F]
    (edgeE : E → Sym2 V) (edgeF : F → Sym2 V) :
    Function.Commute (edgeMean edgeE) (edgeMean edgeF) := by
  intro f
  funext G
  unfold edgeMean
  rw [mean_comm]
  apply mean_congr
  intro d
  apply mean_congr
  intro e
  exact congrArg f (addEdge_comm G (edgeE e) (edgeF d))

theorem edgeMean_add {V E : Type*} [Fintype E] (edge : E → Sym2 V)
    (f g : MGraph V → ℝ) :
    edgeMean edge (fun H => f H + g H) = fun G => edgeMean edge f G + edgeMean edge g G := by
  funext G
  exact mean_add _ _

theorem edgeMean_const_mul {V E : Type*} [Fintype E] (edge : E → Sym2 V)
    (c : ℝ) (f : MGraph V → ℝ) :
    edgeMean edge (fun H => c * f H) = fun G => c * edgeMean edge f G := by
  funext G
  exact mean_const_mul _ _

def globalEdge (n₁ n₂ : ℕ) :
    Fin (n₁ + n₂) × Fin (n₁ + n₂) → Sym2 (Fin (n₁ + n₂)) :=
  fun xy => s(xy.1, xy.2)

def leftEdge (n₁ n₂ : ℕ) : Fin n₁ × Fin n₁ → Sym2 (Fin (n₁ + n₂)) :=
  fun xy => s(leftVertex n₁ n₂ xy.1, leftVertex n₁ n₂ xy.2)

def rightEdge (n₁ n₂ : ℕ) : Fin n₂ × Fin n₂ → Sym2 (Fin (n₁ + n₂)) :=
  fun xy => s(rightVertex n₁ n₂ xy.1, rightVertex n₁ n₂ xy.2)

theorem globalStep_eq_edgeMean (n₁ n₂ : ℕ) :
    globalStep n₁ n₂ = edgeMean (globalEdge n₁ n₂) := rfl

theorem localStep_eq_edgeMeans (n₁ n₂ : ℕ) :
    localStep n₁ n₂ = fun f G =>
      (n₁ : ℝ) / ((n₁ + n₂ : ℕ) : ℝ) * edgeMean (leftEdge n₁ n₂) f G +
      (n₂ : ℝ) / ((n₁ + n₂ : ℕ) : ℝ) * edgeMean (rightEdge n₁ n₂) f G := rfl

theorem globalStep_mono (n₁ n₂ : ℕ) : Monotone (globalStep n₁ n₂) := by
  rw [globalStep_eq_edgeMean]
  exact edgeMean_mono _

theorem localStep_mono (n₁ n₂ : ℕ) (h₁ : 1 ≤ n₁) (h₂ : 1 ≤ n₂) :
    Monotone (localStep n₁ n₂) := by
  intro f g h G
  rw [localStep_eq_edgeMeans]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (edgeMean_mono _ h G)
      (by positivity)
  · exact mul_le_mul_of_nonneg_left (edgeMean_mono _ h G)
      (by positivity)

theorem global_local_commute (n₁ n₂ : ℕ) :
    Function.Commute (globalStep n₁ n₂) (localStep n₁ n₂) := by
  intro f
  funext G
  rw [localStep_eq_edgeMeans]
  rw [globalStep_eq_edgeMean]
  rw [edgeMean_add, edgeMean_const_mul, edgeMean_const_mul]
  have hl := congrFun (edgeMean_commute (globalEdge n₁ n₂) (leftEdge n₁ n₂) f) G
  have hr := congrFun (edgeMean_commute (globalEdge n₁ n₂) (rightEdge n₁ n₂) f) G
  change ((n₁ : ℝ) / ((n₁ + n₂ : ℕ) : ℝ)) *
      edgeMean (globalEdge n₁ n₂) (edgeMean (leftEdge n₁ n₂) f) G +
    ((n₂ : ℝ) / ((n₁ + n₂ : ℕ) : ℝ)) *
      edgeMean (globalEdge n₁ n₂) (edgeMean (rightEdge n₁ n₂) f) G =
    ((n₁ : ℝ) / ((n₁ + n₂ : ℕ) : ℝ)) *
      edgeMean (leftEdge n₁ n₂) (edgeMean (globalEdge n₁ n₂) f) G +
    ((n₂ : ℝ) / ((n₁ + n₂ : ℕ) : ℝ)) *
      edgeMean (rightEdge n₁ n₂) (edgeMean (globalEdge n₁ n₂) f) G
  rw [hl, hr]

theorem iterate_compare_of_commute {X : Type*}
    (A B : (X → ℝ) → (X → ℝ)) (hA : Monotone A) (hB : Monotone B)
    (hcomm : Function.Commute A B) {f : X → ℝ} (hf : B f ≤ A f) (m : ℕ) :
    B^[m] f ≤ A^[m] f := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc
      B (B^[m] f) ≤ B (A^[m] f) := hB ih
      _ = A^[m] (B f) := (hcomm.symm.iterate_right m f)
      _ ≤ A^[m] (A f) := hA.iterate m hf
      _ = A (A^[m] f) := (Function.iterate_succ_apply A m f).symm.trans
        (Function.iterate_succ_apply' A m f)

end ThLean.W.SA50
