import ThLean.BP.S3.Terminal
import ThLean.BP.S3.Lifetime

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
universe u v
namespace ThLean.BP.S3
open ThresholdFoundations

/-- Paper `def:pre-poissonized,lem:pre-tails`; blueprint P1-31. -/
def S3_31Statement : Prop :=
  ∀ z : ℝ, 0 ≤ z →
    (∀ k, 0 ≤ poissonWeight z k) ∧
    Summable (poissonWeight z) ∧ (∑' k, poissonWeight z k) = 1 ∧
    (∀ a : ℝ, 0 ≤ a → Summable (fun k => poissonWeight z k * a^k) ∧
      (∑' k, poissonWeight z k * a^k) = Real.exp (z*(a-1))) ∧
    (∀ k, poissonWeight 0 k = if k = 0 then 1 else 0) ∧
    (0 < z → ∀ k, 0 < poissonWeight z k)

/-- Paper `def:pre-poissonized`; blueprint P1-32. -/
def S3_32Statement : Prop :=
  ∀ (E : Type u) [Fintype E] [Nonempty E] (ν : E → ℝ) (z : ℝ),
    IsProbabilityVector ν → 0 ≤ z →
    Summable (poissonListMass z ν) ∧ (∑' xs : List E, poissonListMass z ν xs) = 1 ∧
    (∀ k : ℕ, (∑' xs : List E, if xs.length = k then poissonListMass z ν xs else 0) =
      poissonWeight z k) ∧
    (∀ k : ℕ, ∀ x : Fin k → E,
      poissonListMass z ν (List.ofFn x) = poissonWeight z k * ∏ i, ν (x i))

/-- Paper `lem:pre-split(a)`; blueprint P1-33. -/
def S3_33Statement : Prop :=
  ∀ (E : Type u) [Fintype E] (label : E → Bool) (u v : List E),
    (∀ e ∈ u, label e = true) → (∀ e ∈ v, label e = false) →
    let A := {w : List E | w.filter label = u ∧ w.filter (fun e => !(label e)) = v}
    A.Finite ∧ A.ncard = (u.length+v.length).choose u.length ∧
    ∀ w ∈ A, w.length = u.length+v.length ∧
      ∀ ν : E → ℝ, (w.map ν).prod = (u.map ν).prod * (v.map ν).prod

/-- Paper `lem:pre-split(a)`; blueprint P1-34. -/
def S3_34Statement : Prop :=
  ∀ (E : Type u) [Fintype E] [Nonempty E] (ν : E → ℝ) (label : E → Bool)
    (z : ℝ), IsProbabilityVector ν → 0 ≤ z →
    let p := ∑ e : E, if label e then ν e else 0
    let r := ∑ e : E, if label e then 0 else ν e
    0 < p → 0 < r → ∀ u v : List E,
    (∀ e ∈ u, label e = true) → (∀ e ∈ v, label e = false) →
    (∑' w : List E, if w.filter label = u ∧ w.filter (fun e => !(label e)) = v
      then poissonListMass z ν w else 0) =
    poissonListMass (z*p) (fun e => ν e / p) u *
      poissonListMass (z*r) (fun e => ν e / r) v

/-- Paper `lem:pre-split(a)`; blueprint P1-35a. -/
def S3_35aStatement : Prop :=
  ∀ (E : Type u) [Fintype E] [Nonempty E] (ν : E → ℝ) (J : ℕ)
    (label : E → Fin J) (z : ℝ), IsProbabilityVector ν → 0 ≤ z →
    (∀ j, 0 < cellMass ν label j) → ∀ ys : Fin J → List E,
    (∀ j, ∀ e ∈ ys j, label e = j) →
    weightedListMean z ν (fun w => indicator (∀ j, splitSublist label j w = ys j)) =
    ∏ j : Fin J, poissonListMass (z * cellMass ν label j)
      (fun e => ν e / cellMass ν label j) (ys j)

/-- Paper `lem:pre-split(a)`; blueprint P1-35b. -/
def S3_35bStatement : Prop :=
  ∀ (E : Type u) [Fintype E] [Nonempty E] (ν : E → ℝ) (J : ℕ)
    (label : E → Fin J) (z : ℝ), IsProbabilityVector ν → 0 ≤ z →
    ∀ j, cellMass ν label j = 0 →
    (∑' w : List E, if splitSublist label j w = [] then poissonListMass z ν w else 0) = 1

/-- Paper `lem:pre-split(a)`; blueprint P1-35. -/
def S3_35Statement : Prop := S3_35aStatement.{u} ∧ S3_35bStatement.{u}
theorem S3_35_assembly (ha : S3_35aStatement.{u}) (hb : S3_35bStatement.{u}) : S3_35Statement.{u} := ⟨ha,hb⟩

/-- Paper `lem:pre-split(a)`; blueprint P1-36S. -/
def S3_36SStatement : Prop :=
  ∀ (J : Type u) [Fintype J] (rate : J → ℝ), (∀ j, 0 ≤ rate j) → ∀ k : ℕ,
    Summable (fun c : J → ℕ => if (∑ j, c j) = k then ∏ j, poissonWeight (rate j) (c j) else 0) ∧
    (∑' c : J → ℕ, if (∑ j, c j) = k then ∏ j, poissonWeight (rate j) (c j) else 0) =
      poissonWeight (∑ j, rate j) k

/-- Paper `lem:pre-split(a)`; blueprint P1-36. -/
def S3_36Statement : Prop :=
  ∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V →
  (∀ (t : ℝ) (G : MGraph V), 0 ≤ t →
    poissonGraphMean t (fun H => indicator (H=G)) =
      independentPoissonGraphMass (pairRate (t / Fintype.card (Pair V))) G) ∧
  (∀ (rate : ℝ) (h : MGraph V → ℝ), 0 ≤ rate → (∀ G, |h G| ≤ 1) →
    independentPoissonGraphMean (pairRate rate) h =
      poissonGraphMean (rate * Fintype.card (Pair V)) h)

/-- Paper `lem:pre-split(b)`; blueprint P1-37a. -/
def S3_37aStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (S₀ : Finset V), 3 ≤ Fintype.card V →
  let S' := Finset.univ \ S₀
  2 ≤ S'.card → ∀ (t : ℝ), 0 ≤ t →
  ∀ (B : MGraph {v : V // v ∈ S'}) (C : MGraph {v : V // v ∈ S₀})
    (ys : {v : V // v ∈ S₀} → List V),
    poissonWordProb t (fun w => inducedGraph (listGraph w) S' = B ∧
      inducedGraph (listGraph w) S₀ = C ∧ ∀ a, neighborList a.val S' w = ys a) =
    poissonGraphMean (t * (S'.card.choose 2) / Fintype.card (Pair V))
      (fun G => indicator (G=B)) *
    poissonGraphMean (t * (S₀.card.choose 2) / Fintype.card (Pair V))
      (fun G => indicator (G=C)) *
    ∏ a : {v : V // v ∈ S₀}, poissonListMass (t * S'.card / Fintype.card (Pair V))
      (fun v : V => if v ∈ S' then 1 / (S'.card : ℝ) else 0) (ys a)

/-- Paper `lem:pre-split(b)`; blueprint P1-37b. -/
def S3_37bStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (S : Finset V), S.card ≤ 1 →
    (∀ G : MGraph V, Loopless G → inducedGraph G S = 0) ∧
    (∀ H : MGraph {v : V // v ∈ S},
      poissonGraphMean 0 (fun G => indicator (G=H)) = indicator (H=0))

/-- Paper `lem:pre-split(b)`; blueprint P1-37. -/
def S3_37Statement : Prop := S3_37aStatement.{u} ∧ S3_37bStatement.{u}
theorem S3_37_assembly (ha : S3_37aStatement.{u}) (hb : S3_37bStatement.{u}) : S3_37Statement.{u} := ⟨ha,hb⟩

/-- Paper `lem:pre-split(c)`; blueprint P1-38a. -/
def S3_38aStatement : Prop :=
  ∀ (V : Type u) [Fintype V] (a : V) (w : List (Pair V)),
    let S := Finset.univ.erase a
    degree (listGraph w) a = (neighborList a S w).length ∧
    listGraph w = mapGraph Subtype.val (inducedGraph (listGraph w) S) +
      (fun e => ((neighborList a S w).filter (fun v => s(a,v)=e)).length)

/-- Paper `lem:pre-split(c)`; blueprint P1-38b. -/
def S3_38bStatement : Prop :=
  ∀ (V : Type u) [Fintype V], 3 ≤ Fintype.card V →
  ∀ (a : V) (t : ℝ), 0 ≤ t → let S := Finset.univ.erase a
  ∀ (B : MGraph {v : V // v ∈ S}) (ys : List V),
    poissonWordProb t (fun w => inducedGraph (listGraph w) S = B ∧ neighborList a S w = ys) =
    poissonGraphMean (((Fintype.card V : ℝ)-2)*t/Fintype.card V) (fun G => indicator (G=B)) *
    poissonListMass (2*t/Fintype.card V)
      (fun v : V => if v ≠ a then 1 / ((Fintype.card V : ℝ)-1) else 0) ys

/-- Paper `lem:pre-split(c)`; blueprint P1-38. -/
def S3_38Statement : Prop := S3_38aStatement.{u} ∧ S3_38bStatement.{u}
theorem S3_38_assembly (ha : S3_38aStatement.{u}) (hb : S3_38bStatement.{u}) : S3_38Statement.{u} := ⟨ha,hb⟩

/-- Paper `lem:pre-split`; blueprint P1-38A. -/
def S3_38AStatement : Prop := S3_32Statement.{u} ∧ S3_35Statement.{u} ∧ S3_37Statement.{u} ∧ S3_38Statement.{u}
theorem S3_38A_assembly (h32 : S3_32Statement.{u}) (h35 : S3_35Statement.{u})
    (h37 : S3_37Statement.{u}) (h38 : S3_38Statement.{u}) : S3_38AStatement.{u} := ⟨h32,h35,h37,h38⟩

/-- Paper `lem:pre-poisson`; blueprint P1-39. -/
def S3_39Statement : Prop :=
  ∀ (V : Type u) [Fintype V], 2 ≤ Fintype.card V →
  ∀ h : MGraph V → ℝ≥0∞,
    Measurable (fun t : ℝ => poissonGraphMeanENN t h) ∧
    (∀ p : ℝ, Measurable (fun t : ℝ => poissonGraphMeanENN (p*t) h)) ∧
    (∀ t : ℝ, 0 ≤ t → poissonListMeanENN t (fun _ : Pair V => 1/Fintype.card (Pair V))
      (fun w => h (listGraph w)) = poissonGraphMeanENN t h) ∧
    (∀ (t : ℝ) (π : Equiv.Perm V), 0 ≤ t →
      poissonGraphMeanENN t (fun G => h (relabel π G)) = poissonGraphMeanENN t h)

/-- Paper `lem:pre-poisson`; blueprint P1-40G. -/
def S3_40GStatement : Prop :=
  ∀ m : ℕ,
    IntegrableOn (fun s : ℝ => s^m * Real.exp (-s)) (Set.Ioi 0) ∧
    Tendsto (fun s : ℝ => s^m * Real.exp (-s)) atTop (nhds 0) ∧
    (∫ s : ℝ in Set.Ioi 0, s^m * Real.exp (-s)) = (m.factorial : ℝ)

/-- Paper `lem:pre-poisson`; blueprint P1-40. -/
def S3_40Statement : Prop :=
  ∀ (p : ℝ) (m : ℕ), 0 < p →
    IntegrableOn (fun t : ℝ => poissonWeight (p*t) m) (Set.Ioi 0) ∧
    (∫ t : ℝ in Set.Ioi 0, poissonWeight (p*t) m) = 1/p

/-- Paper `lem:pre-poisson`; blueprint P1-41a. -/
def S3_41aStatement : Prop :=
  ∀ (a : ℕ → ℝ≥0∞) (p : ℝ), 0 < p →
    (∫⁻ t : ℝ in Set.Ioi 0, poissonMixtureENN (p*t) a) =
      ENNReal.ofReal (1/p) * ∑' m, a m

/-- Paper `lem:pre-poisson`; blueprint P1-41b. -/
def S3_41bStatement : Prop :=
  ∀ (a : ℕ → ℝ) (p : ℝ), (∀ m, 0 ≤ a m) → 0 < p →
    (∑' m, ENNReal.ofReal (a m)) ≠ ⊤ →
    Summable a ∧ IntegrableOn (fun t : ℝ => poissonMixture (p*t) a) (Set.Ioi 0) ∧
    (∫ t : ℝ in Set.Ioi 0, poissonMixture (p*t) a) = (1/p) * ∑' m, a m

/-- Paper `lem:pre-poisson`; blueprint P1-41. -/
def S3_41Statement : Prop := S3_41aStatement ∧ S3_41bStatement
theorem S3_41_assembly (ha : S3_41aStatement) (hb : S3_41bStatement) : S3_41Statement := ⟨ha,hb⟩

end ThLean.BP.S3
