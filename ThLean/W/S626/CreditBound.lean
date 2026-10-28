import ThLean.BP.S6.Credit

noncomputable section
open scoped BigOperators
open ThresholdFoundations ThLean.BP.S6
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S626

private theorem noLoop_iff_not_isDiag {α : Type*} [DecidableEq α]
    (z : Sym2 α) : (∀ v : α, z ≠ s(v, v)) ↔ ¬ z.IsDiag := by
  induction z using Sym2.ind with
  | h a b => simp [eq_comm]

private def pairNoDiagEquiv (n : ℕ) :
    Edge n ≃ {z : Sym2 (Fin n) // ¬ z.IsDiag} where
  toFun p := ⟨p.val, (noLoop_iff_not_isDiag p.val).mp p.property⟩
  invFun p := ⟨p.val, (noLoop_iff_not_isDiag p.val).mpr p.property⟩
  left_inv := by intro p; cases p; rfl
  right_inv := by intro p; cases p; rfl

private theorem edge_card (n : ℕ) : Fintype.card (Edge n) = n.choose 2 := by
  calc
    Fintype.card (Edge n) =
        Fintype.card {z : Sym2 (Fin n) // ¬ z.IsDiag} :=
      Fintype.card_congr (pairNoDiagEquiv n)
    _ = (Fintype.card (Fin n)).choose 2 := Sym2.card_subtype_not_diag
    _ = n.choose 2 := by simp

theorem S6_24bStatement_of_deps
    (h05 : S6_05Statement) (h21 : S6_21Statement)
    (h22a : S6_22aStatement) (h24a : S6_24aStatement) :
    S6_24bStatement := by
  intro n q hn hq G u hG
  rcases h05 n q hn hq G u with
    ⟨hsym, _, _, _, _, _, _, hclass, _⟩
  have hc : 1 ≤ (frozenClass q G u).card := (hclass hG).1
  have hrel := h21 (Fin n) (relation q G u) (frozenClass q G u).card hc hsym
  rcases h22a n q hn hq G u hG with ⟨hcommon, _⟩
  have hcount : ((relation q G u).card : ℝ) ≤
      2 * directCreditSum q G u +
        2 * (((frozenClass q G u).card : ℝ) - 1) *
          sectionMass (relation q G u) (frozenClass q G u).card := by
    rw [← hcommon]
    exact hrel.2
  have hsection : 0 ≤
      sectionMass (relation q G u) (frozenClass q G u).card := by
    unfold sectionMass
    apply Finset.sum_nonneg
    intro a ha
    apply le_min
    · exact div_nonneg (by positivity) (by positivity)
    · norm_num
  have hhalf : ((relation q G u).card : ℝ) / 2 ≤
      directCreditSum q G u +
        (((frozenClass q G u).card : ℝ) - 1) *
          sectionMass (relation q G u) (frozenClass q G u).card := by
    nlinarith
  have hnum : ((relation q G u).card : ℝ) / 2 ≤
      directCreditSum q G u +
        (2 * ((frozenClass q G u).card : ℝ) - 1) *
          sectionMass (relation q G u) (frozenClass q G u).card := by
    have hprod : 0 ≤
        ((frozenClass q G u).card : ℝ) *
          sectionMass (relation q G u) (frozenClass q G u).card :=
      mul_nonneg (by positivity) hsection
    nlinarith
  have hscale : 0 < (n : ℝ) * ((n : ℝ) - 1) := by
    have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
    nlinarith
  have hpairScale : 2 * (Fintype.card (Edge n) : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) := by
    rw [edge_card]
    rw [Nat.cast_choose_two]
    ring
  have hExact := h24a n q hn hq G u hG
  have hav : ((relation q G u).card : ℝ) / 2 ≤
      ((n : ℝ) * ((n : ℝ) - 1)) *
        uniformMean (fun e : Edge n =>
          min (((credited q G u e).card : ℝ) /
            (frozenClass q G u).card) 1) := by
    rw [← hpairScale, hExact]
    exact hnum
  have hcard0 : 0 ≤ ((relation q G u).card : ℝ) := by positivity
  have hn0 : 0 < (n : ℝ) := by positivity
  have hnsub : 0 < (n : ℝ) - 1 := by
    have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
    linarith
  have hdenleft : 0 < 2 * (n : ℝ) ^ 2 := by positivity
  have hdenright : 0 < 2 * (n : ℝ) * ((n : ℝ) - 1) := by positivity
  have hdenorder : 2 * (n : ℝ) * ((n : ℝ) - 1) ≤
      2 * (n : ℝ) ^ 2 := by nlinarith
  have hratio : ((relation q G u).card : ℝ) /
        (2 * (n : ℝ) ^ 2) ≤
      ((relation q G u).card : ℝ) /
        (2 * (n : ℝ) * ((n : ℝ) - 1)) := by
    rw [div_le_div_iff₀ hdenleft hdenright]
    nlinarith [mul_nonneg hcard0 (sub_nonneg.mpr hdenorder)]
  have hratio' : ((relation q G u).card : ℝ) /
        (2 * (n : ℝ) * ((n : ℝ) - 1)) =
      (((relation q G u).card : ℝ) / 2) /
        ((n : ℝ) * ((n : ℝ) - 1)) := by
    field_simp
  have havg : (((relation q G u).card : ℝ) / 2) /
        ((n : ℝ) * ((n : ℝ) - 1)) ≤
      uniformMean (fun e : Edge n =>
        min (((credited q G u e).card : ℝ) /
          (frozenClass q G u).card) 1) := by
    calc
      (((relation q G u).card : ℝ) / 2) /
          ((n : ℝ) * ((n : ℝ) - 1)) ≤
        ((n : ℝ) * ((n : ℝ) - 1) *
          uniformMean (fun e : Edge n =>
            min (((credited q G u e).card : ℝ) /
              (frozenClass q G u).card) 1)) /
          ((n : ℝ) * ((n : ℝ) - 1)) :=
        div_le_div_of_nonneg_right hav (le_of_lt hscale)
      _ = uniformMean (fun e : Edge n =>
          min (((credited q G u e).card : ℝ) /
            (frozenClass q G u).card) 1) := by
        field_simp [ne_of_gt hscale, ne_of_gt hnsub]
  simpa [beta] using (calc
    (((relation q G u).card : ℝ) / (n : ℝ) ^ 2) / 2 =
        ((relation q G u).card : ℝ) / (2 * (n : ℝ) ^ 2) := by ring
    _ ≤ ((relation q G u).card : ℝ) /
        (2 * (n : ℝ) * ((n : ℝ) - 1)) := hratio
    _ = (((relation q G u).card : ℝ) / 2) /
        ((n : ℝ) * ((n : ℝ) - 1)) := hratio'
    _ ≤ uniformMean (fun e : Edge n =>
        min (((credited q G u e).card : ℝ) /
          (frozenClass q G u).card) 1) := havg)

example (h05 : S6_05Statement) (h21 : S6_21Statement)
    (h22a : S6_22aStatement) (h24a : S6_24aStatement) :
    S6_24bStatement := S6_24bStatement_of_deps h05 h21 h22a h24a

end ThLean.W.S626
