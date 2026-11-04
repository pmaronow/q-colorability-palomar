module

public import ThLean.BP.S3.Terminal

@[expose] public section

universe u

namespace ThLean.W.S321

/-- Any two loopless unordered pairs are related by a vertex permutation. -/
theorem S3_19aStatement_holds : ThLean.BP.S3.S3_19aStatement.{u} := by
  unfold ThLean.BP.S3.S3_19aStatement
  intro V _ e f
  obtain ⟨a, b, he⟩ := Sym2.exists.mp ⟨e.val, rfl⟩
  obtain ⟨c, d, hf⟩ := Sym2.exists.mp ⟨f.val, rfl⟩
  have hab : a ≠ b := by
    intro hab'
    apply e.property a
    simpa [hab'] using he
  have hcd : c ≠ d := by
    intro hcd'
    apply f.property c
    simpa [hcd'] using hf
  let src : Fin 2 → V := fun i => if i.val = 0 then a else b
  let dst : Fin 2 → V := fun i => if i.val = 0 then c else d
  have hsrc : Function.Injective src := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [src]
  have hdst : Function.Injective dst := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [dst]
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair src dst hsrc hdst
  refine ⟨π, ?_⟩
  have hπa : π a = c := by simpa [src, dst] using hπ (0 : Fin 2)
  have hπb : π b = d := by simpa [src, dst] using hπ (1 : Fin 2)
  simp [he, hf, hπa, hπb]

end ThLean.W.S321
