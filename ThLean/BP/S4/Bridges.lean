module

public import ThLean.BP.S4.Deletion
public import ThLean.BP.S4.Parameters

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.S4
open ThresholdFoundations

/-- P2-BRIDGE-01(a), finite terminal interval and survival difference; lem:pre-terminal. -/
def S4_BRIDGE_01AStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ L U : ℕ, L ≤ U →
    terminalProb (V := Fin n) q L U (fun _ _ => True) =
      processSurvival (V := Fin n) q L - processSurvival (V := Fin n) q U ∧
    ∀ T : ℕ, U ≤ T →
      terminalProb (V := Fin n) q L U (fun _ _ => True) =
        uniformProb (fun x : EdgeTuple (Fin n) T =>
          L < boundedFailure q x ∧ boundedFailure q x ≤ U)

/-- P2-BRIDGE-01(b), finite/all-time comparison and total death mass; lem:pre-terminal. -/
def S4_BRIDGE_01BStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n →
    (terminalProbability (V := Fin n) q (fun _ _ => True) = 1) ∧
    ∀ L U : ℕ, L ≤ U → ∀ P : MGraph (Fin n) → Pair (Fin n) → Prop,
      0 ≤ terminalProb q L U P ∧ terminalProb q L U P ≤ terminalProbability q P

/-- Finite positivity, event monotonicity and normalization used by P2-BRIDGE-01 and P2-AS-01. -/
def S4_BRIDGE_01CStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ L U : ℕ, L ≤ U →
    (terminalProb (V := Fin n) q L U (fun _ _ => True) ≤ 1) ∧
    (∀ P Q : MGraph (Fin n) → Pair (Fin n) → Prop,
      (∀ G e, P G e → Q G e) → terminalProb q L U P ≤ terminalProb q L U Q) ∧
    (∀ F J : ℕ → MGraph (Fin n) → Pair (Fin n) → ℝ,
      (∀ h G e, L < h → h ≤ U → Loopless G → Colorable q G →
        ¬ Colorable q (addPair G e) → F h G e ≤ J h G e) →
      terminalReal q L U F ≤ terminalReal q L U J)

/-- P2-BRIDGE-01, terminal interval representation and domination. -/
def S4_BRIDGE_01Statement : Prop :=
  S4_BRIDGE_01AStatement ∧ S4_BRIDGE_01BStatement ∧ S4_BRIDGE_01CStatement

theorem S4_BRIDGE_01_assembly (ha : S4_BRIDGE_01AStatement) (hb : S4_BRIDGE_01BStatement)
    (hc : S4_BRIDGE_01CStatement) : S4_BRIDGE_01Statement := ⟨ha,hb,hc⟩

/-- P2-BRIDGE-02, finite-support centered-window law and interval inclusion; thm:intro-window. -/
def S4_BRIDGE_02Statement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ m : ℤ, ∀ a : ℝ, 0 ≤ a →
    (hittingWindowProbability (V := Fin n) q m a =
      ∑' k : ℕ, hittingMass (V := Fin n) q k *
        indicator (|((k+1 : ℕ) : ℝ)-(m : ℝ)| ≤ a)) ∧
    (Set.Finite {k : ℕ | hittingMass (V := Fin n) q k *
      indicator (|((k+1 : ℕ) : ℝ)-(m : ℝ)| ≤ a) ≠ 0}) ∧
    (∀ L U : ℕ, L ≤ U → m = (L : ℤ) → (U : ℝ)+1-L ≤ a →
      terminalProb (V := Fin n) q L (U+1) (fun _ _ => True) ≤
        hittingWindowProbability (V := Fin n) q m a)

/-- P2-BRIDGE-03, finite extended lifetime and all real conversions; lem:pre-lifetime. -/
def S4_BRIDGE_03AStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ G : MGraph (Fin n), Loopless G →
    lifetime q G < ⊤ ∧ Summable (survival q G) ∧
    (∑' k : ℕ, survival q G k) = lifetimeReal q G ∧
    (∀ y : ℝ, 0 ≤ y → (ENNReal.ofReal y < lifetime q G ↔ y < lifetimeReal q G)) ∧
    (∀ a : ℝ, 0 ≤ a →
      (min (ENNReal.ofReal a) (lifetime q G)).toReal = min a (lifetimeReal q G)) ∧
    (¬ Colorable q G → lifetime q G = 0 ∧ lifetimeReal q G = 0)

/-- Finite-window real/extended threshold transport for P2-BRIDGE-03. -/
def S4_BRIDGE_03BStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ L U D : ℕ, L ≤ U →
    ∀ y : ℝ, 0 ≤ y →
      lowWindowProbability (V := Fin n) q L U D y =
        terminalProb (V := Fin n) q L U (fun G e => y < lifetimeReal q G ∧ lowEdge G D e) ∧
      highLongWindowProbability (V := Fin n) q L U D y =
        terminalProb (V := Fin n) q L U (fun G e => y < lifetimeReal q G ∧ bothHigh G D e)

/-- P2-BRIDGE-03, pointwise and finite-window conversions. -/
def S4_BRIDGE_03Statement : Prop := S4_BRIDGE_03AStatement ∧ S4_BRIDGE_03BStatement

theorem S4_BRIDGE_03_assembly (ha : S4_BRIDGE_03AStatement) (hb : S4_BRIDGE_03BStatement) :
    S4_BRIDGE_03Statement := ⟨ha,hb⟩

end ThLean.BP.S4
