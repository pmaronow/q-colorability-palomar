import ThLean.BP.S3.Exports
import ThLean.W.S309.Process
import ThLean.W.S381.Adapters
import ThLean.W.S302.S3_03a
import ThLean.W.S422.TerminalHelpers

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.BR07
open ThresholdFoundations
universe u

private theorem tupleGraph_prefix_subgraph {V : Type*} [Fintype V]
    {m n : ℕ} (ι : Fin m ↪ Fin n) (x : Fin n → Pair V) :
    subgraph (tupleGraph (fun j : Fin m => x (ι j))) (tupleGraph x) := by
  classical
  intro e
  change (Finset.univ.filter (fun j : Fin m => (x (ι j)).val = e)).card ≤
    (Finset.univ.filter (fun j : Fin n => (x j).val = e)).card
  apply Finset.card_le_card_of_injOn ι
  · intro j hj
    rcases Finset.mem_filter.mp hj with ⟨_, hje⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hje⟩
  · intro i hi j hj hij
    exact ι.injective hij

private theorem colorable_of_subgraph_local {V : Type*} [Fintype V] {q : ℕ}
    {G H : MGraph V} (hsub : subgraph G H) (hc : Colorable q H) :
    Colorable q G := by
  rcases hc with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  intro u v huv
  exact hσ u v (lt_of_lt_of_le huv (hsub (s(u, v))))

private theorem processSurvival_antitone_of_projectivity
    {V : Type u} [Fintype V]
    (hproj : ThLean.BP.S3.S3_02Statement.{u})
    (q m n : ℕ) (hmn : m ≤ n) (hpair : Nonempty (Pair V)) :
    processSurvival (V := V) q n ≤ processSurvival (V := V) q m := by
  classical
  letI : Nonempty (Pair V) := hpair
  let ι : Fin m ↪ Fin n :=
    ⟨fun j => ⟨j.val, lt_of_lt_of_le j.isLt hmn⟩,
      fun i j hij => Fin.ext (congrArg (fun z : Fin n => z.val) hij)⟩
  let F : EdgeTuple V m → ℝ := fun x => indicator (Colorable q (tupleGraph x))
  have hproject := (hproj (Pair V) n m ι).2.2.1 F
  have hpoint : ∀ x : EdgeTuple V n,
      indicator (Colorable q (tupleGraph x)) ≤
        indicator (Colorable q (tupleGraph (fun j : Fin m => x (ι j)))) := by
    intro x
    have hsub := tupleGraph_prefix_subgraph ι x
    by_cases hc : Colorable q (tupleGraph x)
    · have hpref : Colorable q (tupleGraph (fun j : Fin m => x (ι j))) :=
        colorable_of_subgraph_local hsub hc
      simp [indicator, hc, hpref]
    · by_cases hpref : Colorable q (tupleGraph (fun j : Fin m => x (ι j)))
      · simp [indicator, hc, hpref]
      · simp [indicator, hc, hpref]
  have hmean_le :
      uniformMean (fun x : EdgeTuple V n => indicator (Colorable q (tupleGraph x))) ≤
        uniformMean (fun x : EdgeTuple V n =>
          indicator (Colorable q (tupleGraph (fun j : Fin m => x (ι j))))) := by
    unfold uniformMean
    have hc : 0 < (Fintype.card (EdgeTuple V n) : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr
        (show Nonempty (EdgeTuple V n) from inferInstance))
    rw [div_le_div_iff_of_pos_right hc]
    exact Finset.sum_le_sum (fun x hx => hpoint x)
  have hmean_eq :
      uniformMean (fun x : EdgeTuple V n =>
          indicator (Colorable q (tupleGraph (fun j : Fin m => x (ι j))))) =
        uniformMean (fun x : EdgeTuple V m => indicator (Colorable q (tupleGraph x))) :=
    hproject
  unfold processSurvival survival uniformProb
  simp only [zero_add]
  exact hmean_le.trans_eq hmean_eq

private theorem processSurvival_zero_time (q n : ℕ) (hq : 1 ≤ q) :
    processSurvival (V := Fin n) q 0 = 1 := by
  have hg (x : EdgeTuple (Fin n) 0) : tupleGraph x = 0 := by
    funext e
    simp [tupleGraph]
  have hc (x : EdgeTuple (Fin n) 0) : Colorable q (tupleGraph x) := by
    rw [hg x]
    exact ThLean.W.S422.colorable_zero_graph q (by omega)
  simp [processSurvival, survival, uniformProb, uniformMean, indicator, hc]

theorem ProjectiveConsistencyStatement_holds :
    ThresholdFoundations.ProjectiveConsistencyStatement := by
  have hfinite : ThresholdFoundations.PreFiniteLawsStatement.{0, 0} :=
    ThLean.BP.S3.PreFiniteLaws_of_S3
      ThLean.W.S309.S3_02Statement_holds
      ThLean.W.S381.S3_02bStatement_holds
      ThLean.W.S302.S3_03aStatement_holds
  refine ⟨hfinite, ?_⟩
  intro q n hq hn
  have hpair : Nonempty (Pair (Fin n)) := ThLean.W.S422.pair_nonempty_fin hn
  refine ⟨?_, processSurvival_zero_time q n hq⟩
  intro m k hmk
  exact processSurvival_antitone_of_projectivity
    ThLean.W.S309.S3_02Statement_holds q m k hmk hpair

example : ThresholdFoundations.ProjectiveConsistencyStatement :=
  ProjectiveConsistencyStatement_holds

end ThLean.W.BR07
