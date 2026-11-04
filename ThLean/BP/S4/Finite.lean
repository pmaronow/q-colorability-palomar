module

public import ThLean.Defs

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.S4
open ThresholdFoundations

/-- P2-FIN-01(a), finite reindexing used in eq:red-cond. -/
def S4_FIN_01AStatement : Prop :=
  ∀ (A B : Type) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (e : A ≃ B) (f : B → ℝ), uniformMean (fun a => f (e a)) = uniformMean f

/-- P2-FIN-01(b), finite Fubini used in eq:red-cond. -/
def S4_FIN_01BStatement : Prop :=
  ∀ (A B : Type) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A × B → ℝ),
    uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a,b)))

/-- P2-FIN-01(c), cylinder invariance used in eq:red-Ysum. -/
def S4_FIN_01CStatement : Prop :=
  ∀ (E : Type) [Fintype E] [Nonempty E] (r s : ℕ) (f : (Fin r → E) → ℝ),
    uniformMean (fun x : Fin (r+s) → E => f (fun i => x ⟨i.val, by omega⟩)) =
      uniformMean f

/-- P2-FIN-01, all finite uniform-law identities used in Section 4. -/
def S4_FIN_01Statement : Prop :=
  S4_FIN_01AStatement ∧ S4_FIN_01BStatement ∧ S4_FIN_01CStatement

theorem S4_FIN_01A_assembly (h : PreFiniteLawsStatement.{0,0}) : S4_FIN_01AStatement := h.1

theorem S4_FIN_01B_assembly (h : PreFiniteLawsStatement.{0,0}) : S4_FIN_01BStatement := h.2.1

theorem S4_FIN_01_assembly (h : PreFiniteLawsStatement.{0,0})
    (hc : S4_FIN_01CStatement) : S4_FIN_01Statement := ⟨h.1,h.2.1,hc⟩

/-- P2-ES-01, square identities and Jensen; proof of lem:red-varlower. -/
def S4_ES_01Statement : Prop :=
  ∀ (A : Type) [Fintype A] [Nonempty A] (f : A → ℝ) (c : ℝ),
    uniformMean (fun a => (f a-c)^2) = variance f + (uniformMean f-c)^2 ∧
    variance f = (1/2 : ℝ) * uniformMean (fun p : A × A => (f p.1-f p.2)^2) ∧
    (uniformMean f)^2 ≤ uniformMean (fun a => (f a)^2)

/-- P2-ES-02, total variance and contraction; proof of lem:red-deletion. -/
def S4_ES_02Statement : Prop :=
  ∀ (A B : Type) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A × B → ℝ),
    variance f = uniformMean (fun a => variance (fun b => f (a,b))) +
      variance (fun a => uniformMean (fun b => f (a,b))) ∧
    variance (fun a => uniformMean (fun b => f (a,b))) ≤
      uniformMean (fun b => variance (fun a => f (a,b)))

/-- P2-ES-03, finite tensorization; proof of lem:red-deletion.
Empty alphabets are included: all means vanish unless the index is empty. -/
def S4_ES_03Statement : Prop :=
  ∀ (I E : Type) [Fintype I] [DecidableEq I] [Fintype E] (f : (I → E) → ℝ),
    variance f ≤ ∑ i : I, uniformMean (fun x : I → E =>
      variance (fun a : E => f (Function.update x i a)))

/-- P2-ES-04, coefficient-one omission inequality; lem:red-deletion.
Omission is expressed by update invariance, avoiding dependent deleted-index types. -/
def S4_ES_04Statement : Prop :=
  ∀ (I E : Type) [Fintype I] [DecidableEq I] [Fintype E] (f : (I → E) → ℝ)
    (g : I → (I → E) → ℝ),
    (∀ i x a, g i (Function.update x i a) = g i x) →
    variance f ≤ ∑ i : I, uniformMean (fun x => (f x-g i x)^2)

/-- P2-RED-12, endpoint-mass lower variance; lem:red-varlower. -/
def S4_RED_12Statement : Prop :=
  ∀ (A : Type) [Fintype A] (f : A → ℝ) (a b : ℝ), a ≤ b →
    uniformProb (fun x => f x=a) * uniformProb (fun x => f x=b) * (b-a)^2 ≤ variance f ∧
    ∀ η : ℝ, 0 ≤ η → η ≤ uniformProb (fun x => f x=a) →
      η ≤ uniformProb (fun x => f x=b) → η^2*(b-a)^2 ≤ variance f

/-- P2-ALG-01, the two minimum estimates; eq:red-minscale and prop:red-split. -/
def S4_ALG_01Statement : Prop :=
  (∀ a w y : ℝ, 0 < a → a ≤ w → 0 ≤ y → min w y ≤ (w/a)*min a y) ∧
  (∀ a x y : ℝ, 0 ≤ a → 0 ≤ x → 0 ≤ y → min a y ≤ x+a*indicator (x<y))

/-- P2-ALG-02, finite-space variance inequality; prop:red-window. -/
def S4_ALG_02AStatement : Prop :=
  ∀ (A : Type) [Fintype A] [Nonempty A] (R : A → ℝ) (P : A → Prop)
    (η a U w B : ℝ), (∀ x, 0 ≤ R x) → 0 < η → 0 < a → 0 ≤ U → 0 ≤ w → 0 ≤ B →
    η^2*w^2 ≤ 2*U*uniformMean (fun x => if P x then min w (R x) else 0) →
    uniformMean (fun x => if P x then min a (R x) else 0) ≤ B →
    w ≤ max a (2*U*B/(η^2*a))

/-- Scalar normalization of P2-ALG-02 for the finite terminal functional.
The conditional scale bound is only used when the window exceeds the cap. -/
def S4_ALG_02BStatement : Prop :=
  ∀ n ε Λ η K U w s t : ℝ,
    0 < n → 0 < ε → 0 ≤ Λ → 0 < η → 0 ≤ K → 0 ≤ U → 0 ≤ w → U ≤ Λ*n →
    η^2*w^2 ≤ 2*U*s → t ≤ K*n*ε^2 →
    (n*ε ≤ w → s ≤ (w/(n*ε))*t) →
    w ≤ max 1 (2*Λ*K/η^2)*n*ε

/-- P2-ALG-02, probability form and terminal-ready scalar form. -/
def S4_ALG_02Statement : Prop := S4_ALG_02AStatement ∧ S4_ALG_02BStatement

theorem S4_ALG_02_assembly (ha : S4_ALG_02AStatement) (hb : S4_ALG_02BStatement) :
    S4_ALG_02Statement := ⟨ha,hb⟩

/-- P2-RED-15, disjoint probability split; prop:red-split. -/
def S4_RED_15AStatement : Prop :=
  ∀ (A : Type) [Fintype A] [Nonempty A] (R : A → ℝ) (P B : A → Prop)
    (s ε : ℝ), (∀ x, 0 ≤ R x) → 0 < s → 0 < ε →
    uniformProb (fun x => P x ∧ s*ε^2 < R x ∧ B x) ≤ ε →
    uniformProb (fun x => P x ∧ s*ε^2 < R x ∧ ¬ B x) ≤ ε →
    uniformMean (fun x => if P x then min (s*ε) (R x) else 0) ≤ 3*s*ε^2

end ThLean.BP.S4
