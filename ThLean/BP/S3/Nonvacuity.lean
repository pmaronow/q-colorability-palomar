import ThLean.BP.S3.Exports

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThLean.BP.S3
open ThresholdFoundations


/-! Concrete witnesses for the guarded families of preliminary statements. -/

example : 3 ≤ (3 : ℕ) ∧ 2*3 ≤ (6 : ℕ) := by norm_num
example : gamma 3 + 1 < gamma 3 + 2 ∧ 0 < (1/4 : ℝ) ∧ (1/4 : ℝ) ≤ 1/2 := by
  constructor
  · linarith
  · norm_num

example : Loopless (0 : MGraph (Fin 6)) ∧ Colorable 3 (0 : MGraph (Fin 6)) := by
  refine ⟨?_,⟨(fun _ => 0),?_⟩⟩
  · intro v; rfl
  · simp [IsColoring]

def samplePair : Pair (Fin 2) := ⟨s(0,1),by decide⟩
example (M : ℕ) : Nonempty (EdgeTuple (Fin 2) M) := ⟨fun _ => samplePair⟩
example : IsProbabilityVector (fun _ : Fin 2 => (1/2 : ℝ)) := by
  constructor
  · intro i; norm_num
  · norm_num [Fin.sum_univ_two]

example : AdmissibleKind 3 (fun (_ : MGraph (Fin 6)) (_ : Pair (Fin 6)) => False) ∧
    kindInvariant (fun (_ : MGraph (Fin 6)) (_ : Pair (Fin 6)) => False) := by
  constructor
  · intro G e h; exact h.elim
  · intro π G e e' h; rfl

example : RelabelInvariantENN (fun _ : MGraph (Fin 6) => 1) := by
  intro π G; rfl
example : 0 < (1 : ℝ) ∧ 0 ≤ (0 : ℝ) ∧ (0 : ℝ) < 1 := by norm_num
example : (2 : ℝ) ≤ 2 ∧ 0 ≤ (1 : ℝ) ∧ 0 ≤ (0 : ℝ) ∧
    (1 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1*2 ∧ (0 : ℝ)*1 ≤ 1 ∧
    (1/2 : ℝ) = (1-1/2)*0+1/2 := by norm_num

def tripleParallel : MGraph (Fin 2) := fun e => if e = s(0,1) then 3 else 0

def parallelPath (i : Fin 3) : OccurrencePath tripleParallel where
  length := 1
  vertex := fun j => j
  edge := fun _ => ⟨s(0,1),⟨i.val,by simpa [tripleParallel] using i.isLt⟩⟩
  vertex_injective := Function.injective_id
  edge_injective := by intro a b h; exact Subsingleton.elim a b
  joins := by intro j; fin_cases j; rfl

example : Loopless tripleParallel := by
  intro v
  fin_cases v <;> decide

example : ExactTheta tripleParallel := by
  classical
  let occ (i : Fin 3) : Occurrence tripleParallel :=
    ⟨s(0,1),⟨i.val,by simpa [tripleParallel] using i.isLt⟩⟩
  have ho (i : Fin 3) : pathOccurrences (parallelPath i) = {occ i} := by
    ext x
    simp only [pathOccurrences,parallelPath,Finset.mem_image,Finset.mem_univ,true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨j,_,hj⟩
      exact hj.symm
    · intro h
      exact ⟨0,Finset.mem_univ _,h.symm⟩
  have hv (i : Fin 3) : pathVertices (parallelPath i) = {0,1} := by
    ext v
    fin_cases v <;> simp [pathVertices,parallelPath] <;> exact Finset.mem_univ _
  have hp (i j : Fin 3) (hij : i ≠ j) :
      Disjoint (pathOccurrences (parallelPath i)) (pathOccurrences (parallelPath j)) ∧
      pathVertices (parallelPath i) ∩ pathVertices (parallelPath j) ⊆ {0,1} := by
    constructor
    · rw [ho,ho,Finset.disjoint_singleton]
      intro h
      apply hij
      apply Fin.ext
      exact congrArg (fun x : Occurrence tripleParallel => x.2.val) h
    · rw [hv,hv]
      exact Finset.inter_subset_left
  refine ⟨0,1,by decide,parallelPath 0,parallelPath 1,parallelPath 2,?_,?_,?_⟩
  · intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨by decide,by constructor <;> rfl⟩
  · constructor
    · intro p hmem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with rfl | rfl
      · simpa only [Finset.subset_iff,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton] using hp 0 1 (by decide)
      · simpa only [Finset.subset_iff,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton] using hp 0 2 (by decide)
    · constructor
      · intro p hmem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        subst p
        simpa only [Finset.subset_iff,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton] using hp 1 2 (by decide)
      · simp
  · ext e
    simp only [ho,Finset.mem_union,Finset.mem_singleton,Finset.mem_univ,iff_true]
    rcases e with ⟨e,i⟩
    have he : e = s(0,1) := by
      by_contra he
      have hi := i.isLt
      simp [tripleParallel,he] at hi
    subst e
    have hi : i.val < 3 := by simpa [tripleParallel] using i.isLt
    have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases hc with h | h | h
    · left; left
      apply congrArg (fun j : Fin (tripleParallel s(0,1)) => (⟨s(0,1),j⟩ : Occurrence tripleParallel))
      exact Fin.ext h
    · left; right
      apply congrArg (fun j : Fin (tripleParallel s(0,1)) => (⟨s(0,1),j⟩ : Occurrence tripleParallel))
      exact Fin.ext h
    · right
      apply congrArg (fun j : Fin (tripleParallel s(0,1)) => (⟨s(0,1),j⟩ : Occurrence tripleParallel))
      exact Fin.ext h

example : 1 ≤ (1 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧ 1+1+1 = (2 : ℕ)+1 := by
  norm_num
example : 2 ≤ (2 : ℕ) ∧ 2 ≤ (2 : ℕ) ∧ 2+2+0 = (3 : ℕ)+1 := by norm_num
example : 0 < (1/4 : ℝ) ∧ (1/4 : ℝ) < 1/2 := by norm_num

end ThLean.BP.S3
