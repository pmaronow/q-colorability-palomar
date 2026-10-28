import ThLean.Defs

noncomputable section
open scoped BigOperators ENNReal
open ThresholdFoundations
attribute [local instance] Classical.propDecidable

namespace ThLean.BP.S6

abbrev Hist (n m : ℕ) := EdgeTuple (Fin n) m
abbrev Graph (n : ℕ) := MGraph (Fin n)
abbrev Edge (n : ℕ) := Pair (Fin n)

def takePrefix {n m M : ℕ} (hm : m ≤ M) (x : Hist n M) : Hist n m :=
  fun i => x ⟨i.val, lt_of_lt_of_le i.isLt hm⟩

def meanGraph {n : ℕ} (m : ℕ) (f : Graph n → ℝ) : ℝ :=
  uniformMean (fun x : Hist n m => f (tupleGraph x))

def degreeMean (n q m j : ℕ) : ℝ := meanGraph (n := n) m (kappaDegree q j)
def npMean (n q m K j : ℕ) : ℝ := meanGraph (n := n) m (kappaDegreeNP q K j)
def pivMean (n q m K j : ℕ) : ℝ := meanGraph (n := n) m (kappaDegreePiv q K j)
def rootEqMean (n q m j : ℕ) (u : Fin n) : ℝ :=
  meanGraph m (fun G => indicator (degree G u = j) * beta q G u)
def rootGeMean (n q m j : ℕ) (u : Fin n) : ℝ :=
  meanGraph m (fun G => indicator (j ≤ degree G u) * beta q G u)

def alpha : ℝ := 1 / 4

/-- The real finite-average rules used in the assemblies. -/
structure MeanRules (A : Type) [Fintype A] : Prop where
  nonneg : ∀ f : A → ℝ, (∀ x, 0 ≤ f x) → 0 ≤ uniformMean f
  mono : ∀ f g : A → ℝ, (∀ x, f x ≤ g x) → uniformMean f ≤ uniformMean g
  add : ∀ f g : A → ℝ, uniformMean (fun x => f x + g x) =
    uniformMean f + uniformMean g
  smul : ∀ (c : ℝ) (f : A → ℝ), uniformMean (fun x => c * f x) = c * uniformMean f
  const : 0 < Fintype.card A → ∀ c : ℝ, uniformMean (fun _ : A => c) = c
  prob : ∀ P : A → Prop, 0 ≤ uniformProb P ∧ uniformProb P ≤ 1

/-- P4-HIGH-01a; finite-average algebra, Section 6 lines 63--67. Paper label: `eq:high-exchange`; blueprint ID: `P4-HIGH-01a`. -/
def S6_01aStatement : Prop := ∀ (A : Type) [Fintype A], MeanRules A

/-- P4-HIGH-01b; prefix and next-coordinate averaging, lines 337--350. Paper label: `eq:high-exchange`; blueprint ID: `P4-HIGH-01b`. -/
def S6_01bStatement : Prop := ∀ n : ℕ, 3 ≤ n →
  (∀ (m M : ℕ) (hm : m ≤ M) (F : Hist n m → ℝ),
    uniformMean (fun x : Hist n M => F (takePrefix hm x)) = uniformMean F) ∧
  (∀ (m : ℕ) (J : Hist n m → ℝ) (Z : Hist n m → Edge n → ℝ),
    uniformMean (fun x : Hist n (m + 1) =>
      J (takePrefix (Nat.le_succ m) x) *
      Z (takePrefix (Nat.le_succ m) x) (x ⟨m, Nat.lt_succ_self m⟩)) =
    uniformMean (fun x : Hist n m => J x * uniformMean (Z x)))

/-- P4-HIGH-01; finite averaging calculus, Section 6 auxiliary infrastructure. Paper label: `eq:high-exchange`; blueprint ID: `P4-HIGH-01`. -/
def S6_01Statement : Prop := S6_01aStatement ∧ S6_01bStatement

theorem S6_01_assembly (ha : S6_01aStatement) (hb : S6_01bStatement) :
    S6_01Statement := ⟨ha, hb⟩

/-- P4-HIGH-03; unordered-pair and endpoint averages, lines 94--99 and 276--279. Paper label: `eq:high-deletion-3`; blueprint ID: `P4-HIGH-03`. -/
def S6_03Statement : Prop := ∀ n : ℕ, 3 ≤ n →
  (∀ z : Fin n → ℝ,
    uniformMean (fun e : Edge n => ∑ a : Fin n, indicator (Touches a e.val) * z a) =
      (2 / (n : ℝ)) * ∑ a : Fin n, z a) ∧
  (∀ h : Sym2 (Fin n) → ℝ,
    uniformMean (fun e : Edge n => h e.val) =
      (∑ a : Fin n, ∑ b : Fin n, indicator (a ≠ b) * h s(a, b)) /
        ((n : ℝ) * ((n : ℝ) - 1))) ∧
  (∀ u : Fin n, uniformProb (fun e : Edge n => Touches u e.val) = 2 / (n : ℝ))

/-- P4-HIGH-04a; degree-density partition and support, eq. high-kappaj. Paper label: `eq:high-kappaj`; blueprint ID: `P4-HIGH-04a`. -/
def S6_04aStatement : Prop := ∀ (n q : ℕ), 3 ≤ n → 3 ≤ q →
  ∀ (G : Graph n) (j K : ℕ), 1 ≤ K →
    0 ≤ kappaDegree q j G ∧ 0 ≤ kappaDegreeNP q K j G ∧
    0 ≤ kappaDegreePiv q K j G ∧
    kappaDegree q j G = kappaDegreeNP q K j G + kappaDegreePiv q K j G ∧
    kappaDegree q j G ≤ kappa q G ∧ kappa q G ≤ 1 ∧
    (edgeCount G < j → kappaDegree q j G = 0 ∧
      kappaDegreeNP q K j G = 0 ∧ kappaDegreePiv q K j G = 0)

/-- P4-HIGH-04b; pivotal occurrence and repeated-edge facts, def. high-pivotal. Paper label: `def:high-pivotal`; blueprint ID: `P4-HIGH-04b`. -/
def S6_04bStatement : Prop := ∀ (n q : ℕ), 3 ≤ n → 3 ≤ q →
  (∀ (G : Graph n) (u v : Fin n) (j K : ℕ), u ≠ v → Frozen q G u v →
    degree G u = j → 1 ≤ K → K ≤ j → nonpivotalCount q G u v < K →
    j - K + 1 ≤ (Finset.univ.filter (fun o : Occurrence G => Pivotal q G u v o)).card) ∧
  (∀ (G : Graph n) (u v : Fin n) (e : Edge n), Frozen q G u v →
    Touches u e.val → 2 ≤ G e.val → Frozen q (erasePair G e) u v) ∧
  (∀ (G : Graph n) (u : Fin n) (e : Edge n), Colorable q G →
    0 < G e.val → Touches u e.val →
    Colorable q (erasePair G e) ∧ degree (erasePair G e) u + 1 = degree G u)

/-- P4-HIGH-04; all density and occurrence facts, def. high-pivotal. Paper label: `def:high-pivotal`; blueprint ID: `P4-HIGH-04`. -/
def S6_04Statement : Prop := S6_04aStatement ∧ S6_04bStatement

theorem S6_04_assembly (ha : S6_04aStatement) (hb : S6_04bStatement) :
    S6_04Statement := ⟨ha, hb⟩

/-- P4-HIGH-05; relation symmetry, sections and bounds, lem. high-relation(a). Paper label: `lem:high-relation(a)`; blueprint ID: `P4-HIGH-05`. -/
def S6_05Statement : Prop := ∀ (n q : ℕ), 3 ≤ n → 3 ≤ q →
  ∀ (G : Graph n) (u : Fin n),
    (∀ a b, (a, b) ∈ relation q G u ↔ (b, a) ∈ relation q G u) ∧
    (∀ a, (a, a) ∉ relation q G u) ∧
    (∀ a, relationSection q G u a ⊆ Finset.univ \ frozenClass q G u) ∧
    (∀ a, a ∈ frozenClass q G u → relationSection q G u a = ∅) ∧
    (relation q G u).card = ∑ a : Fin n, (relationSection q G u a).card ∧
    0 ≤ beta q G u ∧ beta q G u ≤ 1 ∧
    (Colorable q G → 1 ≤ (frozenClass q G u).card ∧ (frozenClass q G u).card ≤ n) ∧
    (¬ Colorable q G → relation q G u = ∅ ∧ beta q G u = 0)

/-- P4-HIGH-06; exact incident-addition class, lem. high-relation(b). Paper label: `lem:high-relation(b)`; blueprint ID: `P4-HIGH-06`. -/
def S6_06Statement : Prop := ∀ (n q : ℕ), 3 ≤ n → 3 ≤ q →
  ∀ (G : Graph n) (u y : Fin n), Colorable q G → y ∉ frozenClass q G u →
    y ≠ u ∧ ∀ e : Edge n, e.val = s(u, y) → Colorable q (addPair G e) ∧
      frozenClass q (addPair G e) u = frozenClass q G u ∪ relationSection q G u y

/-- P4-HIGH-07; rooted relabeling covariance, Section 6 lines 127--129. Paper label: `eq:high-deletion-piv`; blueprint ID: `P4-HIGH-07`. -/
def S6_07Statement : Prop := ∀ (n q : ℕ), 3 ≤ n → 3 ≤ q →
  ∀ (π : Equiv.Perm (Fin n)) (G : Graph n) (u : Fin n) (j K : ℕ), 1 ≤ K →
    (Colorable q (relabel π G) ↔ Colorable q G) ∧
    degree (relabel π G) (π u) = degree G u ∧
    frozenClass q (relabel π G) (π u) = (frozenClass q G u).image π ∧
    relation q (relabel π G) (π u) = (relation q G u).image (fun ab => (π ab.1, π ab.2)) ∧
    beta q (relabel π G) (π u) = beta q G u ∧
    kappaDegree q j (relabel π G) = kappaDegree q j G ∧
    kappaDegreeNP q K j (relabel π G) = kappaDegreeNP q K j G ∧
    kappaDegreePiv q K j (relabel π G) = kappaDegreePiv q K j G ∧
    (∀ (m : ℕ) (F : Graph n → ℝ),
      meanGraph m (fun H => F (relabel π H)) = meanGraph m F) ∧
    (∀ m : ℕ, ∃ ρ : Hist n m ≃ Hist n m,
      (∀ x, tupleGraph (ρ x) = relabel π (tupleGraph x)) ∧
      ∀ F : Hist n m → ℝ, uniformMean (fun x => F (ρ x)) = uniformMean F)

/-- P4-HIGH-08; finite occurrence-deletion exchangeability, eq. high-exchange. Paper label: `eq:high-exchange`; blueprint ID: `P4-HIGH-08`. -/
def S6_08Statement : Prop := ∀ (n m : ℕ), 3 ≤ n → 1 ≤ m →
  ∀ h : Graph n → Edge n → ℝ,
    uniformMean (fun x : Hist n m => ∑ i : Fin m,
      h (erasePair (tupleGraph x) (x i)) (x i)) =
    (m : ℝ) * meanGraph (m - 1) (fun G => uniformMean (h G))

end ThLean.BP.S6
