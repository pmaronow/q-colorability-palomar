module

public import ThLean.BP.S5.Structure
public import ThLean.BP.S5.Elementary

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.BP.S5
open ThresholdFoundations

/-- P3-LOW-08A; pre-split(a): Poissonized words have independent count coordinates. -/
def S5_08AStatement : Prop :=
  ∀ (E : Type) [Fintype E] [Nonempty E] (t : ℝ), 0 ≤ t → ∀ c : E → ℕ,
    HasSum (fun m : ℕ => poissonWeight t m *
      uniformProb (fun x : Fin m → E => ∀ e,
        (Finset.univ.filter (fun i => x i = e)).card = c e))
      (∏ e, poissonWeight (t / Fintype.card E) (c e))

/-- P3-LOW-08B; pre-split(a): histogram and finite-prefix graph laws agree. -/
def S5_08BStatement : Prop :=
  ∀ (V : Type) [Fintype V], 2 ≤ Fintype.card V →
  ∀ t : ℝ, 0 ≤ t → ∀ f : MGraph V → ℝ, (∃ C : ℝ, ∀ G, |f G| ≤ C) →
    poissonGraphMean t f = countMean (t / ((Fintype.card V).choose 2 : ℝ)) f

/-- P3-LOW-08C; pre-split: bounded histogram expectations are measurable in time. -/
def S5_08CStatement : Prop :=
  ∀ (I : Type) [Fintype I] (r : I → ℝ), (∀ i, 0 ≤ r i) →
  ∀ f : (I → ℕ) → ℝ, (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    Measurable (fun t : Set.Ici (0 : ℝ) =>
      ∑' x : I → ℕ, (∏ i, poissonWeight (r i * t.val) (x i)) * f x)

/-- P3-LOW-08; pre-split(a), with its required measurability wrapper. -/
def S5_08Statement : Prop := S5_08AStatement ∧ S5_08BStatement ∧ S5_08CStatement

theorem S5_08_assembly (ha : S5_08AStatement) (hb : S5_08BStatement)
    (hc : S5_08CStatement) : S5_08Statement := ⟨ha, hb, hc⟩

/-- P3-LOW-09A; pre-split(b): disjoint outside, inside, and crossing count blocks. -/
def S5_09AStatement : Prop :=
  ∀ (V : Type) [Fintype V], 3 ≤ Fintype.card V →
  ∀ Z : Finset V, Z.Nonempty → 2 ≤ Fintype.card V - Z.card →
  ∀ t : ℝ, 0 ≤ t → ∀ f : MGraph V → ℝ, (∃ C : ℝ, ∀ G, |f G| ≤ C) →
    poissonGraphMean t f =
      countMean (t / ((Fintype.card V).choose 2 : ℝ))
        (fun B : MGraph {v : V // v ∉ Z} =>
          countMean (t / ((Fintype.card V).choose 2 : ℝ))
            (fun R : MGraph {v : V // v ∈ Z} =>
              ∑' c : ({v : V // v ∈ Z} × {v : V // v ∉ Z}) → ℕ,
                (∏ p, poissonWeight (t / ((Fintype.card V).choose 2 : ℝ)) (c p)) *
                f (mapGraph Subtype.val B + mapGraph Subtype.val R +
                  (fun e => ∑ p, if e = s(p.1.val, p.2.val) then c p else 0))))

/-- P3-LOW-09B; pre-split(c): one root and an independent Poisson neighbor list. -/
def S5_09BStatement : Prop :=
  ∀ (V : Type) [Fintype V], 2 ≤ Fintype.card V →
  ∀ t : ℝ, 0 ≤ t → ∀ f : MGraph (Option V) → ℝ, (∃ C : ℝ, ∀ G, |f G| ≤ C) →
    poissonGraphMean t f =
      poissonGraphMean (((Fintype.card V : ℝ) - 1) / ((Fintype.card V : ℝ) + 1) * t)
        (fun B : MGraph V =>
          poissonMixture (2 * t / ((Fintype.card V : ℝ) + 1))
            (fun j => listMean j (fun xs => f (addRoot B xs))))

/-- P3-LOW-09C; pre-split: aggregate independent crossing counts into one list. -/
def S5_09CStatement : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (D : ℕ) (r : ℝ), 0 ≤ r →
  ∀ f : (V → ℕ) → ℝ, (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    (∑' c : (Fin D × V) → ℕ, (∏ p, poissonWeight r (c p)) *
      f (fun v => ∑ a : Fin D, c (a, v))) =
    poissonMixture (D * Fintype.card V * r) (fun j =>
      uniformMean (fun x : Fin j → V =>
        f (fun v => (Finset.univ.filter (fun i => x i = v)).card)))

/-- P3-LOW-09; pre-split(b,c), including crossing-list aggregation. -/
def S5_09Statement : Prop := S5_09AStatement ∧ S5_09BStatement ∧ S5_09CStatement

theorem S5_09_assembly (ha : S5_09AStatement) (hb : S5_09BStatement)
    (hc : S5_09CStatement) : S5_09Statement := ⟨ha, hb, hc⟩

/-- P3-LOW-10; pre-poisson: nonnegative occupation and justified real conversion. -/
def S5_10Statement : Prop :=
  ∀ p : ℝ, 0 < p →
    (∀ a : ℕ → ℝ≥0∞,
      Measurable (fun t : Set.Ici (0 : ℝ) => poissonMixtureENN (p * t.val) a) ∧
      (∫⁻ t in Set.Ici (0 : ℝ), poissonMixtureENN (p * t) a) =
        ENNReal.ofReal (1 / p) * ∑' m, a m) ∧
    (∀ a : ℕ → ℝ, (∀ m, 0 ≤ a m) → Summable a →
      IntegrableOn (fun t => poissonMixture (p * t) a) (Set.Ici 0) ∧
      (∫ t in Set.Ici (0 : ℝ), poissonMixture (p * t) a) = (1 / p) * ∑' m, a m)

/-- P3-LOW-11; low-added-integral: hazard budget even without almost-sure death. -/
def S5_11Statement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 3 ≤ q → 2 ≤ Fintype.card V →
    HasSum (fun m => uniformMean (fun x : EdgeTuple V m => kappa q (tupleGraph x)))
      (1 - infiniteHittingProbability (V := V) q) ∧
    (∀ p : ℝ, 0 < p →
      IntegrableOn (fun t => poissonGraphMean (p * t) (kappa (V := V) q)) (Set.Ici 0) ∧
      (∫ t in Set.Ici (0 : ℝ), poissonGraphMean (p * t) (kappa (V := V) q)) ≤ 1 / p)

/-- P3-LOW-12; low-class: an exchangeable root has mean partner count (K-1)kappa. -/
def S5_12Statement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 3 ≤ q → 2 ≤ Fintype.card V →
  ∀ ν : PMF (MGraph V), invariantLaw ν → ∀ a : V,
    Summable (fun G => (ν G).toReal * (partnerCount q G a : ℝ)) ∧
    Summable (fun G => (ν G).toReal * kappa q G) ∧
    lawMean ν (fun G => (partnerCount q G a : ℝ)) /
      ((Fintype.card V : ℝ) - 1) = lawMean ν (kappa q)

/-- P3-LOW-13; low-shift/low-class: finite-prefix blocking increments. -/
def S5_13Statement : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (q : ℕ), 3 ≤ q →
  ∀ B : MGraph V, Loopless B →
    blocking q B 0 = 0 ∧
    (∀ j, 0 ≤ increment q B j ∧ increment q B j ≤ 1 ∧
      0 ≤ blocking q B j ∧ blocking q B j ≤ 1 ∧
      blocking q B j = ∑ i ∈ Finset.range j, increment q B i ∧
      increment q B j = (1 / (Fintype.card V : ℝ)) *
        listMean j (fun xs => (partnerCount q (addRoot B xs) none : ℝ)))

/-- P3-LOW-13 helper; low-added: the first-blocking index matches finite-prefix failure. -/
def S5_13AStatement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 3 ≤ q →
  ∀ (B : MGraph V) (x : ℕ → V), Colorable q B →
    (1 : WithTop ℕ) ≤ addedRootHittingTime q B x ∧
    (∀ j : ℕ, addedRootHittingTime q B x ≤ (j : WithTop ℕ) ↔
      ¬ Colorable q (addRoot B (List.ofFn (fun i : Fin j => x i.val))))

/-- P3-LOW-14; eq:low-shift: cumulative blocking versus the next increment. -/
def S5_14Statement : Prop :=
  ∀ a b : ℕ → ℝ, (∀ i, 0 ≤ a i) →
  (∀ j, b j = ∑ i ∈ Finset.range j, a i) → (∀ j, 0 ≤ b j ∧ b j ≤ 1) →
  ∀ z : ℝ, 0 ≤ z →
    Summable (fun j => poissonWeight z j * a j) ∧
    Summable (fun j => poissonWeight z j * b j) ∧
    poissonMixture z b ≤ (Real.exp z - 1) * poissonMixture z a

/-- P3-LOW-15A; low-added: the ordinary added root has the full graph law. -/
def S5_15AStatement : Prop :=
  ∀ (V : Type) [Fintype V], 2 ≤ Fintype.card V →
  ∀ rate s : ℝ, 0 < rate → 0 ≤ s →
  ∀ f : MGraph (Option V) → ℝ, (∃ C : ℝ, ∀ G, |f G| ≤ C) →
    countMean (rate * s) (fun B : MGraph V =>
      poissonMixture (rate * Fintype.card V * s)
        (fun j => listMean j (fun xs => f (addRoot B xs)))) =
    poissonGraphMean (rate * ((Fintype.card V + 1).choose 2 : ℝ) * s) f

/-- P3-LOW-15B; low-class: normalized mean increments and their hazard identity. -/
def S5_15BStatement : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 3 ≤ q → 2 ≤ Fintype.card V →
  ∀ rate s : ℝ, 0 < rate → 0 ≤ s →
    (∀ j, 0 ≤ incrementMean (V := V) q (rate * s) j) ∧
    (∀ j, 0 ≤ blockingMean (V := V) q (rate * s) j ∧
      blockingMean (V := V) q (rate * s) j ≤ 1) ∧
    (∀ j, blockingMean (V := V) q (rate * s) j =
      ∑ i ∈ Finset.range j, incrementMean (V := V) q (rate * s) i) ∧
    poissonMixture (rate * Fintype.card V * s) (incrementMean (V := V) q (rate * s)) =
      poissonGraphMean (V := Option V) (rate * ((Fintype.card V + 1).choose 2 : ℝ) * s) (kappa q)

/-- P3-LOW-15; low-class: full law and averaged killing increments. -/
def S5_15Statement : Prop := S5_15AStatement ∧ S5_15BStatement

theorem S5_15_assembly (ha : S5_15AStatement) (hb : S5_15BStatement) :
    S5_15Statement := ⟨ha, hb⟩

/-- P3-LOW-16; lem:low-added, in the equivalent finite-prefix formulation. -/
def S5_16Statement : Prop :=
  S5_13AStatement ∧ S5_15AStatement ∧
  (∀ (V : Type) [Fintype V] (q : ℕ), 3 ≤ q → 2 ≤ Fintype.card V →
  ∀ rate : ℝ, 0 < rate →
    (∀ s : ℝ, 0 ≤ s →
      addedFailure (V := V) q (rate * s) (rate * Fintype.card V * s) ≤
        (Real.exp (rate * Fintype.card V * s) - 1) *
          poissonGraphMean (V := Option V) (rate * ((Fintype.card V + 1).choose 2 : ℝ) * s) (kappa q)) ∧
    IntegrableOn (fun s =>
      poissonGraphMean (V := Option V) (rate * ((Fintype.card V + 1).choose 2 : ℝ) * s) (kappa q))
      (Set.Ici 0) ∧
    (∫ s in Set.Ici (0 : ℝ),
      poissonGraphMean (V := Option V) (rate * ((Fintype.card V + 1).choose 2 : ℝ) * s) (kappa q)) ≤
        1 / (rate * ((Fintype.card V + 1).choose 2 : ℝ)))

theorem S5_16_assembly (h11 : S5_11Statement) (h13 : S5_13AStatement) (h14 : S5_14Statement)
    (h15 : S5_15Statement) : S5_16Statement := by
  refine ⟨h13, h15.1, ?_⟩
  intro V _ q hq hV rate hrate
  constructor
  · intro s hs
    rcases h15.2 V q hq hV rate s hrate hs with ⟨ha, hb, hc, hd⟩
    have hz : 0 ≤ rate * (Fintype.card V : ℝ) * s := by positivity
    have h := (h14 _ _ ha hc hb _ hz).2.2
    change poissonMixture _ _ ≤ _
    rw [hd] at h
    exact h
  · have hcard : 2 ≤ Fintype.card (Option V) := by
      simp only [Fintype.card_option]
      omega
    have hp : 0 < rate * ((Fintype.card V + 1).choose 2 : ℝ) := by
      have hc : 0 < (Fintype.card V + 1).choose 2 := Nat.choose_pos (by omega)
      positivity
    exact (h11 (Option V) q hq hcard).2 _ hp

end ThLean.BP.S5
