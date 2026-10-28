import ThLean.BP.S4.Objects
import ThLean.BP.S4.Finite

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.S4
open ThresholdFoundations

/-- P2-RED-01(a), clipping equals the survival count; eq:red-Ysum. -/
def S4_RED_01AStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ M L U : ℕ, L ≤ U → U ≤ M →
    ∀ x : EdgeTuple (Fin n) M,
    clippedLast q L U x = L + ∑ m ∈ Finset.Icc (L+1) U,
      if Colorable q (tuplePrefix x m) then 1 else 0

/-- P2-RED-01(b), omission invariance, difference and bounds; eq:red-Ydel. -/
def S4_RED_01BStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ L U : ℕ, L ≤ U →
    (∀ (i : Fin U) (x : EdgeTuple (Fin n) U) (e : Pair (Fin n)),
      deletionYMinus q L i (Function.update x i e) = deletionYMinus q L i x) ∧
    (∀ (i : Fin U) (x : EdgeTuple (Fin n) U),
      (deletionYMinus q L i x : ℝ) - (deletionY q L x : ℝ) =
        ∑ m ∈ Finset.Icc (max (i.val+1) (L+1)) U,
          indicator (deletionDisagreement q x i m)) ∧
    (∀ (i : Fin U) (x : EdgeTuple (Fin n) U),
      0 ≤ (deletionYMinus q L i x : ℝ) - (deletionY q L x : ℝ) ∧
      (deletionYMinus q L i x : ℝ) - (deletionY q L x : ℝ) ≤ (U : ℝ)-L)

/-- P2-RED-01(c), cylinder laws for clipping and each deletion; eq:red-Ysum. -/
def S4_RED_01CStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ M L U : ℕ, L ≤ U → ∀ hUM : U ≤ M,
    (∀ f : ℕ → ℝ,
      uniformMean (fun x : EdgeTuple (Fin n) M => f (clippedLast q L U x)) =
      uniformMean (fun x : EdgeTuple (Fin n) U => f (deletionY q L x))) ∧
    (∀ (i : Fin U) (f : ℕ → ℕ → ℝ),
      uniformMean (fun x : EdgeTuple (Fin n) M =>
        f (clippedLast q L U x)
          (L + ∑ m ∈ Finset.Icc (L+1) U,
            if Colorable q (deletedPrefix x ⟨i.val, lt_of_lt_of_le i.isLt hUM⟩ m)
            then 1 else 0)) =
      uniformMean (fun x : EdgeTuple (Fin n) U => f (deletionY q L x) (deletionYMinus q L i x)))

/-- P2-RED-01, complete capped-variable bookkeeping. -/
def S4_RED_01Statement : Prop :=
  S4_RED_01AStatement ∧ S4_RED_01BStatement ∧ S4_RED_01CStatement

theorem S4_RED_01_assembly (ha : S4_RED_01AStatement) (hb : S4_RED_01BStatement)
    (hc : S4_RED_01CStatement) : S4_RED_01Statement := ⟨ha,hb,hc⟩

/-- P2-RED-02, two-time square expansion; eq:red-square. -/
def S4_RED_02Statement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ L U : ℕ, L ≤ U →
    ∀ (i : Fin U) (x : EdgeTuple (Fin n) U),
    ((deletionYMinus q L i x : ℝ)-(deletionY q L x : ℝ))^2 =
      ∑ m ∈ Finset.Icc (max (i.val+1) (L+1)) U,
        (indicator (deletionDisagreement q x i m) +
          2 * ∑ l ∈ Finset.Icc (m+1) U,
            indicator (deletionDisagreement q x i m ∧ Colorable q (deletedPrefix x i l)))

/-- P2-RED-03, removed-prefix/edge/future product law; eq:red-cond. -/
def S4_RED_03Statement : Prop :=
  ∀ (E : Type) [Fintype E] [Nonempty E] (T m l : ℕ) (i : Fin T)
    (hi : i.val < m) (hm : m ≤ l) (hl : l ≤ T)
    (F : (Fin (m-1) → E) → E → (Fin (l-m) → E) → ℝ),
    uniformMean (fun x : Fin T → E =>
      F (omitBlock x i m hi (le_trans hm hl)) (x i) (futureBlock x m l hm hl)) =
    uniformMean (fun a => uniformMean (fun e => uniformMean (fun b => F a e b)))

/-- P2-RED-04, deterministic two-time average, not conditioning at H-1; eq:red-cond. -/
def S4_RED_04AStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ T m l : ℕ, ∀ i : Fin T,
    i.val < m → m ≤ l → l ≤ T → ∀ a : MGraph (Fin n) → ℝ,
    uniformMean (fun x : EdgeTuple (Fin n) T =>
      a (deletedPrefix x i m) * indicator (deletionDisagreement q x i m) *
        indicator (Colorable q (deletedPrefix x i l))) =
    uniformMean (fun x : EdgeTuple (Fin n) (m-1) =>
      a (tupleGraph x) * kappa q (tupleGraph x) * survival q (tupleGraph x) (l-m))

/-- P2-RED-04 diagonal specialization; eq:red-cond at l=m. -/
def S4_RED_04BStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ T m : ℕ, ∀ i : Fin T,
    i.val < m → m ≤ T →
    uniformMean (fun x : EdgeTuple (Fin n) T => indicator (deletionDisagreement q x i m)) =
      uniformMean (fun x : EdgeTuple (Fin n) (m-1) => kappa q (tupleGraph x))

/-- P2-RED-04, two-time factorization and its diagonal specialization. -/
def S4_RED_04Statement : Prop := S4_RED_04AStatement ∧ S4_RED_04BStatement

theorem S4_RED_04_assembly (ha : S4_RED_04AStatement) (hb : S4_RED_04BStatement) :
    S4_RED_04Statement := ⟨ha,hb⟩

/-- P2-RED-05, guarded nonnegative lifetime weight; eq:red-weight. -/
def S4_RED_05Statement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ m U : ℕ, 1 ≤ m → m ≤ U →
    ∀ G : MGraph (Fin n), Loopless G →
    1 ≤ U+1-m ∧ 0 ≤ deletionWeight q (U+1-m) G ∧
    deletionWeight q (U+1-m) G ≤ (2 : ℝ)*((U+1-m : ℕ) : ℝ)-1 ∧
    kappa q G * deletionWeight q (U+1-m) G =
      kappa q G * (1+2*∑ l ∈ Finset.Icc (m+1) U, survival q G (l-m)) ∧
    (Colorable q G → 1 ≤ deletionWeight q (U+1-m) G ∧
      deletionWeight q (U+1-m) G = 2*truncatedLifetime q (U+1-m) G-1)

/-- P2-RED-06, one omitted occurrence; eq:red-one-i. -/
def S4_RED_06Statement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ L U : ℕ, L ≤ U → ∀ i : Fin U,
    uniformMean (fun x : EdgeTuple (Fin n) U =>
      ((deletionYMinus q L i x : ℝ)-(deletionY q L x : ℝ))^2) =
    ∑ k ∈ Finset.Ico (max i.val L) U,
      uniformMean (fun x : EdgeTuple (Fin n) k =>
        kappa q (tupleGraph x) * deletionWeight q (U-k) (tupleGraph x))

/-- P2-RED-07, summing occurrences gives multiplicity k+1; eq:red-sum-i. -/
def S4_RED_07Statement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ L U : ℕ, L ≤ U →
    (∑ i : Fin U, uniformMean (fun x : EdgeTuple (Fin n) U =>
      ((deletionYMinus q L i x : ℝ)-(deletionY q L x : ℝ))^2)) =
    ∑ k ∈ Finset.Ico L U,
      (k+1 : ℕ) * uniformMean (fun x : EdgeTuple (Fin n) k =>
        kappa q (tupleGraph x) * deletionWeight q (U-k) (tupleGraph x))

/-- P2-RED-08(a), signed finite terminal identity; lem:pre-terminal and eq:red-deletion. -/
def S4_RED_08AStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ L U : ℕ, L ≤ U →
    ∀ F : ℕ → MGraph (Fin n) → ℝ,
    terminalReal q L U (fun h G _ => F h G) =
      ∑ k ∈ Finset.Ico L U, uniformMean (fun x : EdgeTuple (Fin n) k =>
        kappa q (tupleGraph x) * F (k+1) (tupleGraph x))

/-- P2-RED-08(b), bounded finite-word/terminal law, with sentinel guarded; lem:pre-terminal. -/
def S4_RED_08BStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ T L U : ℕ, L ≤ U → U ≤ T →
    ∀ F : ℕ → MGraph (Fin n) → Pair (Fin n) → ℝ,
    uniformMean (terminalSample q L U F : EdgeTuple (Fin n) T → ℝ) = terminalReal q L U F

/-- P2-RED-08, both finite terminal bridges. -/
def S4_RED_08Statement : Prop := S4_RED_08AStatement ∧ S4_RED_08BStatement

theorem S4_RED_08_assembly (ha : S4_RED_08AStatement) (hb : S4_RED_08BStatement) :
    S4_RED_08Statement := ⟨ha,hb⟩

/-- P2-RED-09, exact deletion identity; eq:red-deletion. -/
def S4_RED_09Statement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ L U : ℕ, L ≤ U →
    (∑ i : Fin U, uniformMean (fun x : EdgeTuple (Fin n) U =>
      ((deletionYMinus q L i x : ℝ)-(deletionY q L x : ℝ))^2)) = deletionMoment q n L U

private theorem mean_mul_left {A : Type} [Fintype A] (c : ℝ) (f : A → ℝ) :
    uniformMean (fun x => c*f x) = c*uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum]
  ring

theorem S4_RED_09_assembly (hs : S4_RED_07Statement) (ht : S4_RED_08AStatement) :
    S4_RED_09Statement := by
  intro q n hq hn L U hLU
  rw [hs q n hq hn L U hLU]
  unfold deletionMoment
  rw [ht q n hq hn L U hLU]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← mean_mul_left]
  apply congrArg uniformMean
  funext x
  have hb : U+1-(k+1) = U-k := by omega
  rw [hb]
  by_cases hc : Colorable q (tupleGraph x)
  · simp [deletionWeight, hc]
    ring
  · have hz : kappa q (tupleGraph x) = 0 := by
      simp [kappa, uniformProb, uniformMean, indicator, FrozenPair, Frozen, hc]
    simp [hz]

/-- P2-RED-10(a), pointwise terminal weight bound; eq:red-var-upper. -/
def S4_RED_10AStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ L U h : ℕ, L < h → h ≤ U →
    ∀ (G : MGraph (Fin n)) (e : Pair (Fin n)), Loopless G →
    Colorable q G → ¬ Colorable q (addPair G e) →
    1 ≤ U+1-h ∧ U+1-h ≤ U-L ∧
    0 ≤ (h : ℝ)*(2*truncatedLifetime q (U+1-h) G-1) ∧
    (h : ℝ)*(2*truncatedLifetime q (U+1-h) G-1) ≤
      2*U*min ((U : ℝ)-L) (lifetimeReal q G)

/-- P2-RED-10(b), averaged terminal weight bound; eq:red-var-upper. -/
def S4_RED_10BStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ L U : ℕ, L ≤ U →
    deletionMoment q n L U ≤ 2*U*cappedMoment q n L U ((U : ℝ)-L)

/-- P2-RED-10, pointwise and averaged upper bounds. -/
def S4_RED_10Statement : Prop := S4_RED_10AStatement ∧ S4_RED_10BStatement

theorem S4_RED_10_assembly (ha : S4_RED_10AStatement) (hb : S4_RED_10BStatement) :
    S4_RED_10Statement := ⟨ha,hb⟩

end ThLean.BP.S4
