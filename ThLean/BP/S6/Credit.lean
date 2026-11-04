module

public import ThLean.BP.S6.Foundation

@[expose] public section

noncomputable section
open scoped BigOperators
open ThresholdFoundations
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.S6

/-- Finite relation sections. The carrier may be empty. -/
def sectionOf {V : Type} [Fintype V] (R : Finset (V × V)) (a : V) : Finset V :=
  Finset.univ.filter (fun b => (a, b) ∈ R)
def commonMass {V : Type} [Fintype V] (R : Finset (V × V)) (c : ℕ) : ℝ :=
  ∑ a : V, ∑ b : V, min (((sectionOf R a ∩ sectionOf R b).card : ℝ) / c) 1
def sectionMass {V : Type} [Fintype V] (R : Finset (V × V)) (c : ℕ) : ℝ :=
  ∑ a : V, min (((sectionOf R a).card : ℝ) / c) 1
def largePart {V : Type} [Fintype V] (R : Finset (V × V)) (c : ℕ) : Finset (V × V) :=
  R.filter (fun ab => c ≤ max (sectionOf R ab.1).card (sectionOf R ab.2).card)
def SymmetricRelation {V : Type} (R : Finset (V × V)) : Prop :=
  ∀ a b, (a, b) ∈ R ↔ (b, a) ∈ R

/-- P4-HIGH-17; credited sets and orientation, def. high-credited. Paper label: `def:high-credited`; blueprint ID: `P4-HIGH-17`. -/
def S6_17Statement : Prop := ∀ (n q : ℕ), 3 ≤ n → 3 ≤ q →
  ∀ (G : Graph n) (u : Fin n),
    (∀ a b, creditedAt q G u a b = creditedAt q G u b a) ∧
    (∀ e : Edge n, credited q G u e ⊆ Finset.univ \ frozenClass q G u ∧
      (frozenClass q G u).card + (credited q G u e).card ≤ n) ∧
    (∀ (y : Fin n) (e : Edge n), Colorable q G → y ∉ frozenClass q G u →
      e.val = s(u, y) → credited q G u e = relationSection q G u y)

/-- P4-HIGH-18; absorption of credits, lem. high-absorb. Paper label: `lem:high-absorb`; blueprint ID: `P4-HIGH-18`. -/
def S6_18Statement : Prop := ∀ (n q : ℕ), 3 ≤ n → 3 ≤ q →
  ∀ (G : Graph n) (u : Fin n) (e : Edge n),
    Colorable q G → Colorable q (addPair G e) →
    Disjoint (frozenClass q G u) (credited q G u e) ∧
    frozenClass q G u ⊆ frozenClass q (addPair G e) u ∧
    credited q G u e ⊆ frozenClass q (addPair G e) u ∧
    (frozenClass q G u).card + (credited q G u e).card ≤ (frozenClass q (addPair G e) u).card

/-- P4-HIGH-19; reciprocal double counting, lem. high-comb lines 234--244. Paper label: `lem:high-comb`; blueprint ID: `P4-HIGH-19`. -/
def S6_19Statement : Prop := ∀ (V : Type) [Fintype V]
  (R : Finset (V × V)) (c : ℕ), 1 ≤ c → SymmetricRelation R →
  (∀ a b : V,
    min (((sectionOf R a ∩ sectionOf R b).card : ℝ) / c) 1 =
      ∑ _y ∈ sectionOf R a ∩ sectionOf R b,
        1 / max (c : ℝ) ((sectionOf R a ∩ sectionOf R b).card : ℝ)) ∧
  commonMass R c = ∑ y : V, ∑ a ∈ sectionOf R y, ∑ b ∈ sectionOf R y,
    1 / max (c : ℝ) ((sectionOf R a ∩ sectionOf R b).card : ℝ)

/-- P4-HIGH-20; large sections, eq. high-comb-1. Paper label: `eq:high-comb-1`; blueprint ID: `P4-HIGH-20`. -/
def S6_20Statement : Prop := ∀ (V : Type) [Fintype V]
  (R : Finset (V × V)) (c : ℕ), 1 ≤ c → SymmetricRelation R →
  (∑ ab ∈ R, (((sectionOf R ab.1).card : ℝ) / max (c : ℝ) (sectionOf R ab.2).card +
    ((sectionOf R ab.2).card : ℝ) / max (c : ℝ) (sectionOf R ab.1).card)) ≤
      2 * commonMass R c ∧
  ((largePart R c).card : ℝ) ≤ 2 * commonMass R c

/-- P4-HIGH-21; small sections including c=1, lem. high-comb lines 252--256. Paper label: `lem:high-comb`; blueprint ID: `P4-HIGH-21`. -/
def S6_21Statement : Prop := ∀ (V : Type) [Fintype V]
  (R : Finset (V × V)) (c : ℕ), 1 ≤ c → SymmetricRelation R →
  ((R \ largePart R c).card : ℝ) ≤ 2 * ((c : ℝ) - 1) * sectionMass R c ∧
  (R.card : ℝ) ≤ 2 * commonMass R c + 2 * ((c : ℝ) - 1) * sectionMass R c

/-- P4-HIGH-22a; remove the empty sections on the old class, lem. high-comb. Paper label: `lem:high-comb`; blueprint ID: `P4-HIGH-22a`. -/
def S6_22aStatement : Prop := ∀ (n q : ℕ), 3 ≤ n → 3 ≤ q →
  ∀ (G : Graph n) (u : Fin n), Colorable q G →
    commonMass (relation q G u) (frozenClass q G u).card = directCreditSum q G u ∧
    2 * (((frozenClass q G u).card : ℝ) - 1) *
      sectionMass (relation q G u) (frozenClass q G u).card = crossCreditSum q G u

/-- P4-HIGH-22; graph combinatorial inequality, lem. high-comb. Paper label: `lem:high-comb`; blueprint ID: `P4-HIGH-22`. -/
def S6_22Statement : Prop := ∀ (n q : ℕ), 3 ≤ n → 3 ≤ q →
  ∀ (G : Graph n) (u : Fin n), Colorable q G →
    ((relation q G u).card : ℝ) ≤ 2 * directCreditSum q G u + crossCreditSum q G u

theorem S6_22_assembly (h05 : S6_05Statement) (h21 : S6_21Statement)
    (ha : S6_22aStatement) : S6_22Statement := by
  intro n q hn hq G u hG
  have h := h05 n q hn hq G u
  have hgen := (h21 (Fin n) (relation q G u) (frozenClass q G u).card
    ((h.2.2.2.2.2.2.2.1) hG).1 h.1).2
  obtain ⟨hA, hB⟩ := ha n q hn hq G u hG
  rw [hA, hB] at hgen
  exact hgen

/-- P4-HIGH-23; scalar logarithm lower bound, high-onestep line 270. Paper label: `lem:high-onestep`; blueprint ID: `P4-HIGH-23`. -/
def S6_23Statement : Prop := 0 < Real.log 2 ∧
  ∀ z : ℝ, 0 ≤ z → Real.log 2 * min z 1 ≤ Real.log (1 + z)

/-- P4-HIGH-24a; exact numerator with all root-incident pairs, eq. high-onestep-2. Paper label: `eq:high-onestep-2`; blueprint ID: `P4-HIGH-24a`. -/
def S6_24aStatement : Prop := ∀ (n q : ℕ), 3 ≤ n → 3 ≤ q →
  ∀ (G : Graph n) (u : Fin n), Colorable q G →
    (2 * (Fintype.card (Edge n) : ℝ)) * uniformMean (fun e : Edge n =>
      min (((credited q G u e).card : ℝ) / (frozenClass q G u).card) 1) =
    directCreditSum q G u + (2 * ((frozenClass q G u).card : ℝ) - 1) *
      sectionMass (relation q G u) (frozenClass q G u).card

/-- P4-HIGH-24b; normalized truncated-credit bound, eq. high-onestep-2. Paper label: `eq:high-onestep-2`; blueprint ID: `P4-HIGH-24b`. -/
def S6_24bStatement : Prop := ∀ (n q : ℕ), 3 ≤ n → 3 ≤ q →
  ∀ (G : Graph n) (u : Fin n), Colorable q G →
    beta q G u / 2 ≤ uniformMean (fun e : Edge n =>
      min (((credited q G u e).card : ℝ) / (frozenClass q G u).card) 1)

/-- P4-HIGH-24; exact and normalized truncated credit counts. Paper label: `eq:high-onestep-2`; blueprint ID: `P4-HIGH-24`. -/
def S6_24Statement : Prop := S6_24aStatement ∧ S6_24bStatement

theorem S6_24_assembly (ha : S6_24aStatement) (hb : S6_24bStatement) :
    S6_24Statement := ⟨ha, hb⟩

/-- P4-HIGH-25; all-graph one-step bound, lem. high-onestep. Paper label: `lem:high-onestep`; blueprint ID: `P4-HIGH-25`. -/
def S6_25Statement : Prop := ∀ (n q : ℕ), 3 ≤ n → 3 ≤ q →
  ∀ (G : Graph n) (u : Fin n),
    beta q G u ≤ (2 / Real.log 2) * uniformMean (creditIncrement q G u)

theorem S6_25_assembly (h01 : S6_01aStatement) (h05 : S6_05Statement)
    (h23 : S6_23Statement) (h24 : S6_24bStatement) : S6_25Statement := by
  intro n q hn hq G u
  by_cases hG : Colorable q G
  · have hlow := h24 n q hn hq G u hG
    have hav := (h01 (Edge n)).mono
      (fun e => Real.log 2 * min (((credited q G u e).card : ℝ) / (frozenClass q G u).card) 1)
      (creditIncrement q G u) (fun e => by
        simpa only [creditIncrement, ite_eq_left hG] using
          h23.2 (((credited q G u e).card : ℝ) / (frozenClass q G u).card) (by positivity))
    rw [(h01 (Edge n)).smul] at hav
    have h := (mul_le_mul_of_nonneg_left hlow (le_of_lt h23.1)).trans hav
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ h23.1).2
    nlinarith
  · have hb := (h05 n q hn hq G u).2.2.2.2.2.2.2.2 hG
    simp only [hb.2, creditIncrement, ite_eq_right hG, uniformMean, Finset.sum_const_zero,
      zero_div, mul_zero, le_refl]

end ThLean.BP.S6
