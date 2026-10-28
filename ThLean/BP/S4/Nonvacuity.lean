import ThLean.BP.S4.Objects

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
namespace ThLean.BP.S4
open ThresholdFoundations

/-- The common q,n,Lambda,eta domain is inhabited. -/
example : ∃ (q n : ℕ) (Λ η : ℝ),
    3 ≤ q ∧ 2*q ≤ n ∧ gamma q+1 < Λ ∧ 0 < η ∧ η ≤ etaZero Λ := by
  have hp : 0 < etaZero (gamma 3+2) := div_pos (Real.exp_pos _) (by norm_num)
  refine ⟨3, 6, gamma 3+2, etaZero (gamma 3+2), by norm_num, by norm_num, ?_, hp, le_rfl⟩
  linarith

private def v0 : Fin 6 := ⟨0, by decide⟩
private def v1 : Fin 6 := ⟨1, by decide⟩
private def v2 : Fin 6 := ⟨2, by decide⟩
private def v3 : Fin 6 := ⟨3, by decide⟩
private def witnessEdge : Pair (Fin 6) := ⟨s(v0,v1), by decide⟩
private def witnessGraph : MGraph (Fin 6) := fun e =>
  if e=s(v0,v2) ∨ e=s(v0,v3) ∨ e=s(v1,v2) ∨ e=s(v1,v3) ∨ e=s(v2,v3) then 1 else 0
private def witnessColor (v : Fin 6) : Fin 3 := if v=v2 then 1 else if v=v3 then 2 else 0

/-- A genuine terminal triple: K4 missing one edge, plus two isolated vertices. -/
example : ∃ (G : MGraph (Fin 6)) (e : Pair (Fin 6)),
    Loopless G ∧ Colorable 3 G ∧ ¬ Colorable 3 (addPair G e) := by
  refine ⟨witnessGraph, witnessEdge, ?_, ?_, ?_⟩
  · intro v
    fin_cases v <;> norm_num [witnessGraph, v0, v1, v2, v3, Sym2.eq_iff]
  · refine ⟨witnessColor, ?_⟩
    intro u v h
    fin_cases u <;> fin_cases v
    all_goals try norm_num [witnessGraph, v0, v1, v2, v3, Sym2.eq_iff] at h
    all_goals norm_num [witnessColor, v0, v1, v2, v3]
  · intro ⟨σ, hσ⟩
    let f : Fin 4 → Fin 3 := fun i => σ ⟨i.val, by omega⟩
    have hf : Function.Injective f := by
      intro i j hij
      by_contra hne
      have he : 0 < addPair witnessGraph witnessEdge
          s((⟨i.val, by omega⟩ : Fin 6), (⟨j.val, by omega⟩ : Fin 6)) := by
        fin_cases i <;> fin_cases j
        all_goals try exact (hne rfl).elim
        all_goals norm_num [addPair, addEdge, witnessGraph, witnessEdge, v0, v1, v2, v3,
          Sym2.eq_iff, Function.update]
      exact (hσ _ _ he) hij
    have hc := Fintype.card_le_of_injective f hf
    norm_num at hc

/-- Zero coordinates form a nonempty singleton even over an empty alphabet. -/
example : Nonempty (Fin 0 → Empty) := ⟨fun i => Fin.elim0 i⟩

/-- Positive scalar parameters and a zero-width boundary case coexist. -/
example : ∃ n ε Λ η K U w s t : ℝ,
    0 < n ∧ 0 < ε ∧ 0 ≤ Λ ∧ 0 < η ∧ 0 ≤ K ∧ 0 ≤ U ∧ 0 ≤ w ∧
    U ≤ Λ*n ∧ η^2*w^2 ≤ 2*U*s ∧ t ≤ K*n*ε^2 ∧
    (n*ε ≤ w → s ≤ (w/(n*ε))*t) := by
  refine ⟨1,1,1,1,0,0,0,0,0,?_⟩
  norm_num

end ThLean.BP.S4
