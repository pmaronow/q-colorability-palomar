module

public import ThLean.BP.S4.Deletion

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S414
open ThresholdFoundations
open ThLean.BP.S4

private theorem interval_square_indicator
    (a b : ℕ) (f : ℕ → ℝ) (g : ℕ → ℕ → ℝ)
    (hdiag : ∀ m, f m ^ 2 = f m)
    (hcross : ∀ m l, m < l → f m * f l = g m l) :
    (∑ m ∈ Finset.Icc a b, f m) ^ 2 =
      ∑ m ∈ Finset.Icc a b,
        (f m + 2 * ∑ l ∈ Finset.Icc (m+1) b, g m l) := by
  induction b with
  | zero =>
      by_cases ha : a = 0
      · subst a
        simp [hdiag]
      · have hpos : 0 < a := Nat.pos_of_ne_zero ha
        have he : Finset.Icc a 0 = ∅ := Finset.Icc_eq_empty_of_lt hpos
        simp [he]
  | succ b ih =>
      by_cases hab : a ≤ b
      · have hsplit : Finset.Icc a (b+1) = insert (b+1) (Finset.Icc a b) := by
          exact (Finset.insert_Icc_right_eq_Icc_succ
            (a := a) (b := b) (Nat.le_succ_of_le hab)).symm
        have hnew : b+1 ∉ Finset.Icc a b := by simp
        have hinner : ∀ m, m ∈ Finset.Icc a b →
            Finset.Icc (m+1) (b+1) = insert (b+1) (Finset.Icc (m+1) b) := by
          intro m hm
          have hmb : m ≤ b := (Finset.mem_Icc.mp hm).2
          exact (Finset.insert_Icc_right_eq_Icc_succ
            (a := m+1) (b := b) (Nat.succ_le_succ hmb)).symm
        have hOldRhs :
            (∑ m ∈ Finset.Icc a b,
              (f m + 2 * ∑ l ∈ Finset.Icc (m+1) (b+1), g m l)) =
            (∑ m ∈ Finset.Icc a b,
              (f m + 2 * ∑ l ∈ Finset.Icc (m+1) b, g m l)) +
              2 * ∑ m ∈ Finset.Icc a b, g m (b+1) := by
          calc
            _ = ∑ m ∈ Finset.Icc a b,
                ((f m + 2 * ∑ l ∈ Finset.Icc (m+1) b, g m l) +
                  2 * g m (b+1)) := by
                    apply Finset.sum_congr rfl
                    intro m hm
                    rw [hinner m hm, Finset.sum_insert]
                    · ring
                    · simp
            _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        have hcrossSum :
            (∑ m ∈ Finset.Icc a b, f m) * f (b+1) =
              ∑ m ∈ Finset.Icc a b, g m (b+1) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro m hm
          apply hcross
          have hm' := (Finset.mem_Icc.mp hm).2
          omega
        have hRhs :
            (∑ m ∈ Finset.Icc a (b+1),
              (f m + 2 * ∑ l ∈ Finset.Icc (m+1) (b+1), g m l)) =
            (∑ m ∈ Finset.Icc a b,
              (f m + 2 * ∑ l ∈ Finset.Icc (m+1) b, g m l)) +
              f (b+1) + 2 * ∑ m ∈ Finset.Icc a b, g m (b+1) := by
          rw [hsplit, Finset.sum_insert hnew]
          have hempty : Finset.Icc ((b+1)+1) (b+1) = ∅ := by simp
          simp only [hempty, Finset.sum_empty, mul_zero, add_zero]
          rw [hOldRhs]
          ring
        calc
          (∑ m ∈ Finset.Icc a (b+1), f m) ^ 2 =
              ((∑ m ∈ Finset.Icc a b, f m) + f (b+1)) ^ 2 := by
                rw [hsplit, Finset.sum_insert hnew]
                ring
          _ = (∑ m ∈ Finset.Icc a b,
                (f m + 2 * ∑ l ∈ Finset.Icc (m+1) b, g m l)) +
                f (b+1) + 2 * ∑ m ∈ Finset.Icc a b, g m (b+1) := by
                  nlinarith [ih, hdiag (b+1), hcrossSum]
          _ = ∑ m ∈ Finset.Icc a (b+1),
                (f m + 2 * ∑ l ∈ Finset.Icc (m+1) (b+1), g m l) := hRhs.symm
      · by_cases heq : a = b+1
        · subst a
          simp [hdiag]
        · have hlt : b+1 < a := by omega
          have he : Finset.Icc a (b+1) = ∅ := Finset.Icc_eq_empty_of_lt hlt
          simp [he]

private theorem tuplePrefix_subgraph {V : Type*} [Fintype V] {M : ℕ}
    (x : EdgeTuple V M) {m l : ℕ} (hml : m ≤ l) :
    subgraph (tuplePrefix x m) (tuplePrefix x l) := by
  intro e
  unfold tuplePrefix
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact ⟨lt_of_lt_of_le hj.1 hml, hj.2⟩

private theorem colorable_of_subgraph {V : Type*} [Fintype V]
    {q : ℕ} {G G' : MGraph V} (hsub : subgraph G G')
    (hcol : Colorable q G') : Colorable q G := by
  rcases hcol with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  intro u v huv
  apply hσ u v
  exact lt_of_lt_of_le huv (hsub (s(u,v)))

theorem S4_RED_02Statement_of_deps
    (hred : S4_RED_01BStatement) : S4_RED_02Statement := by
  intro q n hq hn L U hLU i x
  let D : ℕ → Prop := deletionDisagreement q x i
  let C : ℕ → Prop := fun l => Colorable q (deletedPrefix x i l)
  let a := max (i.val+1) (L+1)
  have hsum := (hred q n hq hn L U hLU).2.1 i x
  have hdiag : ∀ m, indicator (D m) ^ 2 = indicator (D m) := by
    intro m
    simp [indicator]
  have hcross : ∀ m l, m < l →
      indicator (D m) * indicator (D l) = indicator (D m ∧ C l) := by
    intro m l hml
    have hnot : D m → ¬ Colorable q (tuplePrefix x l) := by
      intro hm hc
      exact hm.2 (colorable_of_subgraph
        (tuplePrefix_subgraph x (Nat.le_of_lt hml)) hc)
    have hequiv : (D m ∧ D l) ↔ (D m ∧ C l) := by
      constructor
      · rintro ⟨hm, hl⟩
        exact ⟨hm, hl.1⟩
      · rintro ⟨hm, hl⟩
        exact ⟨hm, hl, hnot hm⟩
    by_cases hm : D m
    · by_cases hl : D l
      · have hlC : C l := by
          change Colorable q (deletedPrefix x i l) ∧
            ¬ Colorable q (tuplePrefix x l) at hl
          exact hl.1
        simp [indicator, hm, hl, hlC]
      · have hnC : ¬ C l := by
          intro hc
          apply hl
          change Colorable q (deletedPrefix x i l) ∧
            ¬ Colorable q (tuplePrefix x l)
          exact ⟨hc, hnot hm⟩
        simp [indicator, hm, hl, hnC]
    · simp [indicator, hm]
  have hsquare := interval_square_indicator a U
    (fun m => indicator (D m))
    (fun m l => indicator (D m ∧ C l))
    hdiag hcross
  rw [← hsum] at hsquare
  simpa [D, C, a] using hsquare

end ThLean.W.S414
