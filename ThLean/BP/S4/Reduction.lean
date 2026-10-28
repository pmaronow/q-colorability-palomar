import ThLean.BP.S4.Bridges

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.S4
open ThresholdFoundations

/-- P2-RED-11, stronger arbitrary-cutoff form; lem:red-deletion. -/
def S4_RED_11Statement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ L U : ℕ, L ≤ U →
    (∑ i : Fin U, uniformMean (fun x : EdgeTuple (Fin n) U =>
      ((deletionYMinus q L i x : ℝ)-(deletionY q L x : ℝ))^2)) = deletionMoment q n L U ∧
    variance (fun x : EdgeTuple (Fin n) U => (deletionY q L x : ℝ)) ≤
      2*U*cappedMoment q n L U ((U : ℝ)-L)

theorem S4_RED_11_assembly (he : S4_ES_04Statement) (hi : S4_RED_01BStatement)
    (hd : S4_RED_09Statement) (hu : S4_RED_10BStatement) : S4_RED_11Statement := by
  intro q n hq hn L U hLU
  have he' := he (Fin U) (Pair (Fin n))
    (fun x => (deletionY q L x : ℝ))
    (fun i x => (deletionYMinus q L i x : ℝ)) (by
      intro i x a
      exact congrArg (fun k : ℕ => (k : ℝ)) ((hi q n hq hn L U hLU).1 i x a))
  have hd' := hd q n hq hn L U hLU
  refine ⟨hd', ?_⟩
  have he'' : variance (fun x : EdgeTuple (Fin n) U => (deletionY q L x : ℝ)) ≤
      ∑ i : Fin U, uniformMean (fun x : EdgeTuple (Fin n) U =>
        ((deletionYMinus q L i x : ℝ)-(deletionY q L x : ℝ))^2) := by
    simpa only [sub_sq_comm] using he'
  exact he''.trans (hd'.le.trans (hu q n hq hn L U hLU))

/-- Endpoint masses on W_U including an empty window; P2-RED-13, lem:red-varlower. -/
def S4_RED_13AStatement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, gamma q+1 < Λ → ∀ n : ℕ, 2*q ≤ n →
    ∀ η : ℝ, 0 < η → η ≤ etaZero Λ →
    let L := lowerLocation q Λ η n
    let U := upperLocation q Λ η n
    L ≤ U ∧ U ≤ cap Λ n ∧
    η ≤ uniformProb (fun x : EdgeTuple (Fin n) U => (deletionY q L x : ℝ) = (L : ℝ)) ∧
    η ≤ uniformProb (fun x : EdgeTuple (Fin n) U => (deletionY q L x : ℝ) = (U : ℝ))

/-- P2-RED-13, quantile variance lower bound; lem:red-varlower. -/
def S4_RED_13Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, gamma q+1 < Λ → ∀ n : ℕ, 2*q ≤ n →
    ∀ η : ℝ, 0 < η → η ≤ etaZero Λ →
    η^2*(window q Λ η n)^2 ≤
      variance (fun x : EdgeTuple (Fin n) (upperLocation q Λ η n) =>
        (deletionY q (lowerLocation q Λ η n) x : ℝ))

theorem S4_RED_13_assembly (he : S4_RED_12Statement) (hm : S4_RED_13AStatement) :
    S4_RED_13Statement := by
  intro q hq Λ hΛ n hn η hη hη0
  rcases hm q hq Λ hΛ n hn η hη hη0 with ⟨hLU, hUM, hL, hU⟩
  exact (he (EdgeTuple (Fin n) (upperLocation q Λ η n))
    (fun x => (deletionY q (lowerLocation q Λ η n) x : ℝ))
    (lowerLocation q Λ η n : ℝ) (upperLocation q Λ η n : ℝ)
    (Nat.cast_le.mpr hLU)).2 η hη.le hL hU

/-- Terminal cap rescaling used by P2-RED-14; eq:red-minscale. -/
def S4_RED_14AStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ L U : ℕ, L ≤ U →
    ∀ a w : ℝ, 0 < a → a ≤ w →
    cappedMoment q n L U w ≤ (w/a)*cappedMoment q n L U a

/-- P2-RED-14, capped moment implies a window bound; prop:red-window. -/
def S4_RED_14Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, gamma q+1 < Λ → ∀ n : ℕ, 2*q ≤ n →
    ∀ η : ℝ, 0 < η → η ≤ etaZero Λ → ∀ K : ℝ, 0 ≤ K →
    cappedMoment q n (lowerLocation q Λ η n) (upperLocation q Λ η n)
      ((n : ℝ)*epsilon n) ≤ K*n*epsilon n^2 →
    window q Λ η n ≤ max 1 (2*Λ*K/η^2)*n*epsilon n

theorem S4_RED_14_assembly (ha : S4_ALG_02BStatement) (hs : S4_RED_14AStatement)
    (hv : S4_RED_11Statement) (hl : S4_RED_13Statement) (hm : S4_RED_13AStatement)
    (hp : S4_PAR_01AStatement) (he : S4_PAR_03Statement) : S4_RED_14Statement := by
  intro q hq Λ hΛ n hn η hη hη0 K hK hmoment
  rcases hm q hq Λ hΛ n hn η hη hη0 with ⟨hLU, hUM, hL, hU⟩
  rcases (hp q hq).2.2.2 Λ hΛ with ⟨hΛ1, hη00, hηhalf, hcoef, hcap⟩
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hw : 0 ≤ window q Λ η n := sub_nonneg.mpr (Nat.cast_le.mpr hLU)
  apply ha (n : ℝ) (epsilon n) Λ η K (upperLocation q Λ η n : ℝ)
    (window q Λ η n)
    (cappedMoment q n (lowerLocation q Λ η n) (upperLocation q Λ η n) (window q Λ η n))
    (cappedMoment q n (lowerLocation q Λ η n) (upperLocation q Λ η n) ((n : ℝ)*epsilon n))
    hn0 (he.1 n).1 (by linarith) hη hK (Nat.cast_nonneg _) hw
    ((Nat.cast_le.mpr hUM).trans (hcap n))
  · exact (hl q hq Λ hΛ n hn η hη hη0).trans (hv q n hq hn _ _ hLU).2
  · exact hmoment
  · intro hscale
    exact hs q n hq hn _ _ hLU _ _ (mul_pos hn0 (he.1 n).1) hscale

/-- P2-RED-15, split bound for the finite terminal subprobability; prop:red-split. -/
def S4_RED_15BStatement : Prop :=
  ∀ q n : ℕ, 3 ≤ q → 2*q ≤ n → ∀ L U : ℕ, L ≤ U →
    ∀ s ε : ℝ, 0 < s → 0 < ε → ∀ B : MGraph (Fin n) → Pair (Fin n) → Prop,
    terminalProb q L U (fun G e => s*ε^2 < lifetimeReal q G ∧ B G e) ≤ ε →
    terminalProb q L U (fun G e => s*ε^2 < lifetimeReal q G ∧ ¬ B G e) ≤ ε →
    cappedMoment q n L U (s*ε) ≤ 3*s*ε^2

/-- P2-RED-15, uniform-probability and finite-terminal versions. -/
def S4_RED_15Statement : Prop := S4_RED_15AStatement ∧ S4_RED_15BStatement

theorem S4_RED_15_assembly (ha : S4_RED_15AStatement) (hb : S4_RED_15BStatement) :
    S4_RED_15Statement := ⟨ha,hb⟩

/-- P2-RED-16, exact degree partition and stronger high-edge event; prop:red-split. -/
def S4_RED_16Statement : Prop :=
  ∀ (V : Type) [Fintype V] (G : MGraph V) (e : Pair V) (D : ℕ),
    (lowEdge G D e ↔ ¬ bothHigh G D e) ∧ (bothHigh G D e → highEdge G D e) ∧
    ∀ u v : V, e.val = s(u,v) →
      (lowEdge G D e ↔ min (degree G u) (degree G v) ≤ D) ∧
      (bothHigh G D e ↔ D < min (degree G u) (degree G v)) ∧
      (highEdge G D e ↔ D < max (degree G u) (degree G v))

/-- P2-RED-17, low/both-high split closes the reduction; prop:red-split. -/
def S4_RED_17Statement : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ Λ : ℝ, gamma q+1 < Λ → ∀ n : ℕ, 2*q ≤ n →
    ∀ η : ℝ, 0 < η → η ≤ etaZero Λ →
    let L := lowerLocation q Λ η n
    let U := upperLocation q Λ η n
    terminalProb (V := Fin n) q L U
      (fun G e => lifetimeCut n < lifetimeReal q G ∧ lowEdge G (degreeCut n) e) ≤ epsilon n →
    terminalProb (V := Fin n) q L U
      (fun G e => lifetimeCut n < lifetimeReal q G ∧ bothHigh G (degreeCut n) e) ≤ epsilon n →
    cappedMoment q n L U ((n : ℝ)*epsilon n) ≤ 3*n*epsilon n^2 ∧
    window q Λ η n ≤ (6*Λ/η^2)*n*epsilon n

theorem S4_RED_17_assembly (hs : S4_RED_15BStatement) (hw : S4_RED_14Statement)
    (hd : S4_RED_16Statement) (hm : S4_RED_13AStatement) (hp : S4_PAR_01AStatement)
    (he : S4_PAR_03Statement) : S4_RED_17Statement := by
  intro q hq Λ hΛ n hn η hη hη0
  dsimp only
  intro hlow hhigh
  have hLU := (hm q hq Λ hΛ n hn η hη hη0).1
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hpred :
      (fun (G : MGraph (Fin n)) (e : Pair (Fin n)) =>
        (n : ℝ)*epsilon n^2 < lifetimeReal q G ∧ ¬ lowEdge G (degreeCut n) e) =
      (fun G e => lifetimeCut n < lifetimeReal q G ∧ bothHigh G (degreeCut n) e) := by
    funext G e
    apply propext
    have hh := (hd (Fin n) G e (degreeCut n)).1
    simp only [lifetimeCut]
    tauto
  have hmoment := hs q n hq hn _ _ hLU (n : ℝ) (epsilon n) hn0 (he.1 n).1
    (fun G e => lowEdge G (degreeCut n) e) (by simpa only [lifetimeCut] using hlow)
    (by rw [hpred]; exact hhigh)
  refine ⟨hmoment, ?_⟩
  have hb := hw q hq Λ hΛ n hn η hη hη0 3 (by norm_num) hmoment
  have hc := ((hp q hq).2.2.2 Λ hΛ).2.2.2.1 η hη hη0
  have hnum : 2*Λ*3/η^2 = 6*Λ/η^2 := by ring
  rw [hnum, max_eq_right hc.1] at hb
  exact hb

end ThLean.BP.S4
