import ThLean.W.S340S.Atoms
import ThLean.W.S333.S3_32
import ThLean.W.S334.Shuffle
import ThLean.W.S335.PoissonSplit
import ThLean.W.S336.PoissonSplit

noncomputable section
open scoped BigOperators
open ThresholdFoundations hiding neighborList
open ThLean.BP.S3
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S340S
universe u
set_option maxHeartbeats 800000

theorem poissonGraph_nonloop {V : Type u} [Fintype V] (t : ℝ)
    (G : MGraph V) (hG : ¬ Loopless G) :
    poissonGraphMean t (fun H => indicator (H = G)) = 0 := by
  obtain ⟨v,hv⟩ : ∃ v, G (s(v,v)) ≠ 0 := not_forall.mp hG
  have hx (m : ℕ) (x : EdgeTuple V m) : tupleGraph x ≠ G := by
    intro h
    have hh := congrFun h (s(v,v))
    rw [ThLean.W.S339.tupleGraph_loop_zero] at hh
    exact hv hh.symm
  simp [poissonGraphMean,poissonMixture,uniformMean,indicator,hx]

theorem poissonWordProb_impossible {V : Type u} [Fintype V] (t : ℝ)
    (P : List (Pair V) → Prop) (hP : ∀ w, ¬ P w) : poissonWordProb t P = 0 := by
  simp [poissonWordProb,poissonMixture,uniformProb,uniformMean,indicator,hP]

/-- Block and neighbor-list splitting, using the general finite splitting leaf. -/
theorem S3_37aStatement_of_deps (h35 : S3_35aStatement.{u}) : S3_37aStatement.{u} := by
  intro V _ S hV
  dsimp only
  intro hS t ht B C ys
  by_cases hB : Loopless B
  · by_cases hC : Loopless C
    · by_cases hy : ∀ (a : Inside S) v, v ∈ ys a → v ∈ Finset.univ \ S
      · exact split_loopless h35 S (by omega) (by omega) t ht B C hB hC ys hy
      · push Not at hy
        obtain ⟨a,v,hv,hn⟩ := hy
        have hmass : poissonListMass
            (t * (Finset.univ \ S).card / Fintype.card (Pair V))
            (fun v : V => if v ∈ Finset.univ \ S then
              1 / ((Finset.univ \ S).card : ℝ) else 0) (ys a) = 0 := by
          have hp : ((ys a).map (fun v : V => if v ∈ Finset.univ \ S then
              1 / ((Finset.univ \ S).card : ℝ) else 0)).prod = 0 := by
            apply List.prod_eq_zero_iff.mpr
            exact List.mem_map.mpr ⟨v,hv,by simp [hn]⟩
          rw [poissonListMass,hp,mul_zero]
        have hprod : (∏ a : Inside S, poissonListMass
            (t * (Finset.univ \ S).card / Fintype.card (Pair V))
            (fun v : V => if v ∈ Finset.univ \ S then
              1 / ((Finset.univ \ S).card : ℝ) else 0) (ys a)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ a) hmass
        rw [hprod,mul_zero]
        apply poissonWordProb_impossible
        intro w hw
        apply hn
        apply neighborList_mem a.val (Finset.univ \ S) w v
        rw [hw.2.2 a]
        exact hv
    · rw [poissonGraph_nonloop _ C hC,mul_zero,zero_mul]
      apply poissonWordProb_impossible
      intro w hw
      apply hC
      rw [← hw.2.1]
      exact induced_listGraph_loopless S w
  · rw [poissonGraph_nonloop _ B hB,zero_mul,zero_mul]
    apply poissonWordProb_impossible
    intro w hw
    apply hB
    rw [← hw.1]
    exact induced_listGraph_loopless (Finset.univ \ S) w

/-- The original blueprint leaf, with all splitting dependencies discharged. -/
theorem S3_37aStatement_holds : ThLean.BP.S3.S3_37aStatement.{u} :=
  S3_37aStatement_of_deps
    (ThLean.W.S336.S3_35aStatement_of_deps
      (ThLean.W.S333.S3_32Statement_of_deps ThLean.W.S332.S3_31Statement_holds)
      (ThLean.W.S335.S3_34Statement_of_deps ThLean.W.S334.S3_33Statement_holds))

example : ThLean.BP.S3.S3_37aStatement.{u} := S3_37aStatement_holds

end ThLean.W.S340S
