module

public import ThLean.W.S339.Poisson
public import ThLean.W.S339.ListMean

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S339
open ThresholdFoundations
open ThLean.BP.S3

universe u

theorem S3_36Statement_of_deps
    (h31 : ThLean.BP.S3.S3_31Statement)
    (h32 : ThLean.BP.S3.S3_32Statement.{u})
    (h35a : ThLean.BP.S3.S3_35aStatement.{u}) :
    ThLean.BP.S3.S3_36Statement.{u} := by
  intro V inst hV
  constructor
  · intro t G ht
    exact poissonGraph_pointMass_of_s35a h31 h35a hV t ht G
  · intro rate h hrate hbnd
    letI : Nonempty (Pair V) := pair_nonempty_of_card_ge_two hV
    let N : ℕ := Fintype.card (Pair V)
    have hN : 0 < N := Fintype.card_pos
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    have hRate : rate * (N : ℝ) / (N : ℝ) = rate := by field_simp
    let t : ℝ := rate * (N : ℝ)
    have ht : 0 ≤ t := by dsimp [t]; positivity
    let ν : Pair V → ℝ := fun _ => 1 / (N : ℝ)
    have hν : IsProbabilityVector ν := by
      constructor
      · intro p
        dsimp [ν]
        positivity
      · calc
          (∑ p : Pair V, ν p) = (N : ℝ) * (1 / (N : ℝ)) := by simp [ν, N]
          _ = 1 := by field_simp
    have hMass := (h32 (Pair V) ν t hν ht).1
    have hMassNonneg : ∀ xs : List (Pair V), 0 ≤ poissonListMass t ν xs := by
      intro xs
      unfold poissonListMass
      have hprod : 0 ≤ (xs.map ν).prod := by
        induction xs with
        | nil => simp
        | cons p xs ih =>
            simp only [List.map_cons, List.prod_cons]
            exact mul_nonneg (hν.1 p) ih
      exact mul_nonneg ((h31 t ht).1 xs.length) hprod
    have hFiberMass : ∀ G : MGraph V,
        (∑' xs : {xs : List (Pair V) // listGraph xs = G},
          poissonListMass t ν xs.val) =
          independentPoissonGraphMass (pairRate rate) G := by
      intro G
      have hfiber := tsum_fiberwise_mul
        (fun xs : List (Pair V) => poissonListMass t ν xs)
        (fun xs => listGraph xs)
        (fun H : MGraph V => indicator (H = G))
        hMassNonneg hMass (by intro H; by_cases hh : H = G <;> simp [indicator, hh])
      have hcollapse :
          (∑' H : MGraph V,
            (∑' xs : {xs : List (Pair V) // listGraph xs = H},
              poissonListMass t ν xs.val) * indicator (H = G)) =
            ∑' xs : {xs : List (Pair V) // listGraph xs = G},
              poissonListMass t ν xs.val := by
        calc
          _ = (∑' xs : {xs : List (Pair V) // listGraph xs = G},
                poissonListMass t ν xs.val) * indicator (G = G) := by
              exact tsum_eq_single G (by
                intro H hHG
                simp [indicator, hHG])
          _ = ∑' xs : {xs : List (Pair V) // listGraph xs = G},
                poissonListMass t ν xs.val := by simp [indicator]
      have hAtom : poissonGraphMean t (fun H : MGraph V => indicator (H = G)) =
          ∑' xs : List (Pair V),
            poissonListMass t ν xs * indicator (listGraph xs = G) := by
        calc
          _ = weightedListMean t ν (fun xs => indicator (listGraph xs = G)) := by
            symm
            simpa [ν, N] using
              weightedListMean_uniform_eq_poissonGraphMean t
                (fun H : MGraph V => indicator (H = G))
          _ = _ := weightedListMean_eq_listTsum h31 h32 ν t hν ht
                (fun xs => indicator (listGraph xs = G)) (by intro xs; by_cases hh : listGraph xs = G <;> simp [indicator, hh])
      calc
        (∑' xs : {xs : List (Pair V) // listGraph xs = G}, poissonListMass t ν xs.val) =
            (∑' H : MGraph V,
              (∑' xs : {xs : List (Pair V) // listGraph xs = H},
                poissonListMass t ν xs.val) * indicator (H = G)) := hcollapse.symm
        _ = ∑' xs : List (Pair V),
              poissonListMass t ν xs * indicator (listGraph xs = G) := hfiber.symm
        _ = poissonGraphMean t (fun H : MGraph V => indicator (H = G)) := hAtom.symm
        _ = independentPoissonGraphMass (pairRate (t / (Fintype.card (Pair V) : ℝ))) G :=
              poissonGraph_pointMass_of_s35a h31 h35a hV t ht G
        _ = independentPoissonGraphMass (pairRate rate) G := by
              rw [show t / (Fintype.card (Pair V) : ℝ) = rate by
                dsimp [t, N]
                exact hRate]
    calc
      independentPoissonGraphMean (pairRate rate) h =
          ∑' G : MGraph V,
            (∑' xs : {xs : List (Pair V) // listGraph xs = G},
              poissonListMass t ν xs.val) * h G := by
        unfold independentPoissonGraphMean
        apply tsum_congr
        intro G
        rw [hFiberMass G]
      _ = ∑' xs : List (Pair V), poissonListMass t ν xs * h (listGraph xs) :=
        (tsum_fiberwise_mul
          (fun xs : List (Pair V) => poissonListMass t ν xs)
          (fun xs => listGraph xs) h hMassNonneg hMass hbnd).symm
      _ = weightedListMean t ν (fun xs => h (listGraph xs)) :=
        (weightedListMean_eq_listTsum h31 h32 ν t hν ht
          (fun xs => h (listGraph xs)) (by intro xs; exact hbnd (listGraph xs))).symm
      _ = poissonGraphMean (rate * Fintype.card (Pair V)) h := by
        simpa [t, N, ν] using
          weightedListMean_uniform_eq_poissonGraphMean t h

end ThLean.W.S339
