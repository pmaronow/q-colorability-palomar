import ThLean.BP.S6.Foundation

noncomputable section
open scoped BigOperators
open ThresholdFoundations
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.S6

/-- P4-HIGH-09; non-pivotal incidence count, high-deletion proof lines 84--91. Paper label: `eq:high-deletion-1`; blueprint ID: `P4-HIGH-09`. -/
def S6_09Statement : Prop := ∀ (n q m j K : ℕ),
  3 ≤ n → 3 ≤ q → 1 ≤ m → 1 ≤ j → 1 ≤ K → ∀ x : Hist n m,
    (K : ℝ) * n * ((n : ℝ) - 1) * kappaDegreeNP q K j (tupleGraph x) ≤
      ∑ i : Fin m, nonpivotalDeletionCount q j (erasePair (tupleGraph x) (x i)) (x i)

/-- P4-HIGH-10; fresh non-pivotal average, high-deletion proof lines 94--102. Paper label: `eq:high-deletion-np`; blueprint ID: `P4-HIGH-10`. -/
def S6_10Statement : Prop := ∀ (n q j : ℕ), 3 ≤ n → 3 ≤ q → 1 ≤ j →
  ∀ G : Graph n, uniformMean (nonpivotalDeletionCount q j G) ≤
    (2 / (n : ℝ)) * n * ((n : ℝ) - 1) * kappaDegree q (j - 1) G

/-- P4-HIGH-11; lem. high-deletion(a), with arbitrary positive K. Paper label: `lem:high-deletion(a)`; blueprint ID: `P4-HIGH-11`. -/
def S6_11Statement : Prop := ∀ (n q m j K : ℕ),
  3 ≤ n → 3 ≤ q → 1 ≤ m → 1 ≤ j → 1 ≤ K →
    npMean n q m K j ≤ (2 * m / ((n : ℝ) * K)) * degreeMean n q (m - 1) (j - 1)

theorem S6_11_assembly (h01 : S6_01aStatement) (h08 : S6_08Statement)
    (h09 : S6_09Statement) (h10 : S6_10Statement) : S6_11Statement := by
  intro n q m j K hn hq hm hj hK
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hc : 0 < (K : ℝ) * n * ((n : ℝ) - 1) := by positivity
  have hi := (h01 (Hist n m)).mono _ _ (h09 n q m j K hn hq hm hj hK)
  rw [(h01 (Hist n m)).smul, h08 n m hn hm] at hi
  have hf := (h01 (Hist n (m - 1))).mono _ _
    (fun x => h10 n q j hn hq hj (tupleGraph x))
  rw [(h01 (Hist n (m - 1))).smul] at hf
  change (K : ℝ) * n * ((n : ℝ) - 1) * npMean n q m K j ≤
    (m : ℝ) * meanGraph (m - 1) (fun G => uniformMean (nonpivotalDeletionCount q j G)) at hi
  change meanGraph (m - 1) (fun G => uniformMean (nonpivotalDeletionCount q j G)) ≤
    (2 / (n : ℝ)) * n * ((n : ℝ) - 1) * degreeMean n q (m - 1) (j - 1) at hf
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    (K : ℝ) * n * ((n : ℝ) - 1) * npMean n q m K j ≤
        (m : ℝ) * ((2 / (n : ℝ)) * n * ((n : ℝ) - 1) * degreeMean n q (m - 1) (j - 1)) :=
      hi.trans (mul_le_mul_of_nonneg_left hf (by positivity))
    _ = (K : ℝ) * n * ((n : ℝ) - 1) *
        ((2 * m / ((n : ℝ) * K)) * degreeMean n q (m - 1) (j - 1)) := by
      field_simp [ne_of_gt hn0, ne_of_gt hK0]

/-- P4-HIGH-12; pivotal incidence count, high-deletion proof lines 104--111. Paper label: `eq:high-deletion-2`; blueprint ID: `P4-HIGH-12`. -/
def S6_12Statement : Prop := ∀ (n q m j K : ℕ),
  3 ≤ n → 3 ≤ q → 1 ≤ m → 1 ≤ K → K ≤ j → ∀ x : Hist n m,
    ((j - K + 1 : ℕ) : ℝ) * n * ((n : ℝ) - 1) * kappaDegreePiv q K j (tupleGraph x) ≤
      ∑ i : Fin m, pivotalDeletionCount q j (erasePair (tupleGraph x) (x i)) (x i)

/-- P4-HIGH-13; new partners equal a section, eq. high-deletion-3. Paper label: `eq:high-deletion-3`; blueprint ID: `P4-HIGH-13`. -/
def S6_13Statement : Prop := ∀ (n q : ℕ), 3 ≤ n → 3 ≤ q →
  ∀ (G : Graph n) (a y : Fin n) (e : Edge n), a ≠ y → e.val = s(a, y) →
    (Finset.univ.filter (fun v => a ≠ v ∧ Frozen q (addPair G e) a v ∧
      ¬ Frozen q G a v)).card = (relationSection q G a y).card

/-- P4-HIGH-14; fresh pivotal average, high-deletion proof lines 119--125. Paper label: `eq:high-deletion-piv`; blueprint ID: `P4-HIGH-14`. -/
def S6_14Statement : Prop := ∀ (n q j : ℕ), 3 ≤ n → 3 ≤ q → 1 ≤ j →
  ∀ G : Graph n, uniformMean (pivotalDeletionCount q j G) =
    (2 * n / ((n : ℝ) - 1)) *
      ∑ a : Fin n, indicator (degree G a = j - 1) * beta q G a

/-- P4-HIGH-15; fixed-root expectation by symmetry, lines 127--129. Paper label: `eq:high-deletion-piv`; blueprint ID: `P4-HIGH-15`. -/
def S6_15Statement : Prop := ∀ (n q m j : ℕ), 3 ≤ n → 3 ≤ q → 1 ≤ j →
  ∀ u : Fin n,
    meanGraph m (fun G => ∑ a : Fin n, indicator (degree G a = j - 1) * beta q G a) =
      (n : ℝ) * rootEqMean n q m (j - 1) u

/-- P4-HIGH-16; lem. high-deletion(b), retaining the finite-size correction. Paper label: `lem:high-deletion(b)`; blueprint ID: `P4-HIGH-16`. -/
def S6_16Statement : Prop := ∀ (n q m j K : ℕ),
  3 ≤ n → 3 ≤ q → 1 ≤ m → 1 ≤ K → K ≤ j → ∀ u : Fin n,
    pivMean n q m K j ≤
      (2 * m * n / (((n : ℝ) - 1) ^ 2 * (j - K + 1 : ℕ))) *
        rootEqMean n q (m - 1) (j - 1) u

theorem S6_16_assembly (h01 : S6_01aStatement) (h08 : S6_08Statement)
    (h12 : S6_12Statement) (h14 : S6_14Statement) (h15 : S6_15Statement) :
    S6_16Statement := by
  intro n q m j K hn hq hm hK hj u
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hj0 : (0 : ℝ) < (j - K + 1 : ℕ) := by positivity
  have hc : 0 < ((j - K + 1 : ℕ) : ℝ) * n * ((n : ℝ) - 1) := by positivity
  have hi := (h01 (Hist n m)).mono _ _ (h12 n q m j K hn hq hm hK hj)
  rw [(h01 (Hist n m)).smul, h08 n m hn hm] at hi
  have he : meanGraph (n := n) (m - 1) (fun G => uniformMean (pivotalDeletionCount q j G)) =
      (2 * n / ((n : ℝ) - 1)) * ((n : ℝ) * rootEqMean n q (m - 1) (j - 1) u) := by
    unfold meanGraph
    simp_rw [h14 n q j hn hq (by omega)]
    rw [(h01 (Hist n (m - 1))).smul]
    exact congrArg ((2 * n / ((n : ℝ) - 1)) * ·) (h15 n q (m - 1) j hn hq (by omega) u)
  change ((j - K + 1 : ℕ) : ℝ) * n * ((n : ℝ) - 1) * pivMean n q m K j ≤
    (m : ℝ) * meanGraph (m - 1) (fun G => uniformMean (pivotalDeletionCount q j G)) at hi
  rw [he] at hi
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    _ ≤ _ := hi
    _ = ((j - K + 1 : ℕ) : ℝ) * n * ((n : ℝ) - 1) *
        ((2 * m * n / (((n : ℝ) - 1) ^ 2 * (j - K + 1 : ℕ))) *
          rootEqMean n q (m - 1) (j - 1) u) := by
      field_simp [ne_of_gt hn0, ne_of_gt hn1, ne_of_gt hj0]

end ThLean.BP.S6
