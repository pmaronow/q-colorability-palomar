module

public import ThLean.BP.S6.Potential

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open ThresholdFoundations MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.S6

local instance edgeMeasurable (n : ℕ) : MeasurableSpace (Edge n) := ⊤
local instance edgeSingletons (n : ℕ) : MeasurableSingletonClass (Edge n) := ⟨fun _ => trivial⟩

def inputPrefix {n : ℕ} {Ω : Type} (e : ℕ → Ω → Edge n) (M : ℕ) (ω : Ω) : Hist n M :=
  fun i => e i.val ω

def UniformInputs {n m : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (e : Fin m → Ω → Edge n) : Prop :=
  (∀ i, Measurable (e i)) ∧ iIndepFun e μ ∧
  ∀ (i : Fin m) (f : Edge n), μ.real {ω | e i ω = f} = 1 / (Fintype.card (Edge n) : ℝ)

def UniformStream {n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (e : ℕ → Ω → Edge n) : Prop :=
  ∀ M : ℕ, UniformInputs μ (fun i : Fin M => e i.val)

def InputStoppingTime {n : ℕ} {Ω : Type} (e : ℕ → Ω → Edge n)
    (T : Ω → WithTop ℕ) : Prop :=
  ∀ m : ℕ, MeasurableSet[MeasurableSpace.comap (inputPrefix e m) ⊤]
    {ω | T ω ≤ (m : WithTop ℕ)}

def sampledOccupation {n : ℕ} {Ω : Type} (q M : ℕ) (u : Fin n)
    (e : ℕ → Ω → Edge n) (T : Ω → WithTop ℕ) (ω : Ω) : ℝ :=
  ∑ m ∈ Finset.range M,
    if T ω ≤ (m : WithTop ℕ) ∧ Colorable q (processGraph (fun i => e i ω) m)
    then beta q (processGraph (fun i => e i ω) m) u else 0

def sampledActive {n : ℕ} {Ω : Type} (q M : ℕ)
    (e : ℕ → Ω → Edge n) (T : Ω → WithTop ℕ) (ω : Ω) : Prop :=
  T ω < stoppedTime q M (fun i => e i ω)

/-- P4-HIGH-02a; iid prefix atoms have uniform mass, pre-process. Paper label: `def:pre-process`; blueprint ID: `P4-HIGH-02a`. -/
def S6_02aStatement : Prop := ∀ (n m : ℕ), 3 ≤ n →
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e : Fin m → Ω → Edge n), UniformInputs μ e →
    ∀ x : Hist n m,
      μ.real {ω | (fun i => e i ω) = x} = 1 / (Fintype.card (Hist n m) : ℝ)

/-- P4-HIGH-02b; finite uniform atom law to real integration and probability. Paper label: `def:pre-process`; blueprint ID: `P4-HIGH-02b`. -/
def S6_02bStatement : Prop := ∀ (A Ω : Type) [Fintype A]
  [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A), Measurable X →
  (∀ a : A, μ.real {ω | X ω = a} = 1 / (Fintype.card A : ℝ)) →
  (∀ F : A → ℝ, Measurable (F ∘ X) ∧ Integrable (F ∘ X) μ ∧
    (∫ ω, F (X ω) ∂μ) = uniformMean F) ∧
  (∀ P : A → Prop, MeasurableSet {ω | P (X ω)} ∧
    μ.real {ω | P (X ω)} = uniformProb P)

/-- P4-HIGH-02; complete iid realization bridge. Paper label: `def:pre-process`; blueprint ID: `P4-HIGH-02`. -/
def S6_02Statement : Prop := S6_02aStatement ∧ S6_02bStatement

theorem S6_02_assembly (ha : S6_02aStatement) (hb : S6_02bStatement) :
    S6_02Statement := ⟨ha, hb⟩

/-- P4-HIGH-29a; factor a raw-filtration stopping rule through finite histories.
The cap includes a possible killing edge. No finiteness of H is assumed. Paper label: `thm:high-potential`; blueprint ID: `P4-HIGH-29a`. -/
def S6_29aStatement : Prop := ∀ (n q M : ℕ), 3 ≤ n → 3 ≤ q →
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e : ℕ → Ω → Edge n) (T : Ω → WithTop ℕ) (u : Fin n),
    UniformStream μ e → InputStoppingTime e T →
    ∃ S : Hist n M → WithTop ℕ, IsFiniteStoppingTime S ∧
      (∀ ω, sampledOccupation q M u e T ω = stoppedOccupation q u S (inputPrefix e M ω)) ∧
      (∀ ω, sampledActive q M e T ω ↔ activeStart q S (inputPrefix e M ω))

/-- P4-HIGH-29; thm. high-potential for every iid probability-space realization. Paper label: `thm:high-potential`; blueprint ID: `P4-HIGH-29`. -/
def S6_29Statement : Prop := ∀ (n q M : ℕ), 3 ≤ n → 3 ≤ q →
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e : ℕ → Ω → Edge n) (T : Ω → WithTop ℕ) (u : Fin n),
    UniformStream μ e → InputStoppingTime e T →
    Measurable (sampledOccupation q M u e T) ∧
    Integrable (sampledOccupation q M u e T) μ ∧
    MeasurableSet {ω | sampledActive q M e T ω} ∧
    (∫ ω, sampledOccupation q M u e T ω ∂μ) ≤
      (2 / Real.log 2) * Real.log n * μ.real {ω | sampledActive q M e T ω}

theorem S6_29_assembly (h02a : S6_02aStatement) (h02b : S6_02bStatement)
    (h28 : S6_28Statement) (ha : S6_29aStatement) : S6_29Statement := by
  intro n q M hn hq Ω _ μ _ e T u he hT
  obtain ⟨S, hS, hval, hevent⟩ := ha n q M hn hq Ω μ e T u he hT
  have hmeas : Measurable (inputPrefix e M) := Measurable.of_eval (fun i => (he M).1 i)
  obtain ⟨hi, hp⟩ := h02b (Hist n M) Ω μ (inputPrefix e M) hmeas
    (h02a n M hn Ω μ _ (he M))
  have hfun : sampledOccupation q M u e T = (stoppedOccupation q u S) ∘ inputPrefix e M :=
    funext hval
  have hset : {ω | sampledActive q M e T ω} = {ω | activeStart q S (inputPrefix e M ω)} :=
    Set.ext hevent
  rw [hfun, hset]
  exact ⟨(hi _).1, (hi _).2.1, (hp _).1, by
    simp only [Function.comp_apply]
    rw [(hi _).2.2, (hp _).2]
    exact h28 n q M hn hq u S hS⟩

end ThLean.BP.S6
