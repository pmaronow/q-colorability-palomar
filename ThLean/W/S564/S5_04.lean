import ThLean.BP.S5.Structure

noncomputable section

namespace ThLean.W.S564

open ThresholdFoundations

private theorem identify_pos_iff {V : Type*} [Fintype V]
    (F : MGraph V) (Z : Finset V) (e : Sym2 (QuotientVertices Z)) :
    0 < identify F Z e ↔
      ∃ d : Sym2 V, 0 < F d ∧ Sym2.map (identifyVertex Z) d = e := by
  classical
  unfold identify mapGraph
  rw [Finset.sum_pos_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d, hd⟩
    by_cases he : Sym2.map (identifyVertex Z) d = e
    · exact ⟨d, by simpa [he] using hd, he⟩
    · simp [he] at hd
  · rintro ⟨d, hd, he⟩
    exact ⟨d, by simpa [he] using hd⟩

private noncomputable def quotientColoringFrom {V : Type*} [Fintype V]
    {q : ℕ} (Z : Finset V) (z : V) (σ : V → Fin q) :
    QuotientVertices Z → Fin q :=
  fun x => x.elim (σ z) (fun v => σ v.val)

private theorem quotientColoringFrom_identifyVertex {V : Type*} [Fintype V]
    {q : ℕ} (Z : Finset V) (z : V) (hz : z ∈ Z) (σ : V → Fin q)
    (hconst : constantOn σ Z) (v : V) :
    quotientColoringFrom Z z σ (identifyVertex Z v) = σ v := by
  by_cases hv : v ∈ Z
  · simp [quotientColoringFrom, identifyVertex, hv]
    exact hconst z hz v hv
  · simp [quotientColoringFrom, identifyVertex, hv]

private noncomputable def identificationColoringEquiv {V : Type*} [Fintype V]
    (q : ℕ) (F : MGraph V) (Z : Finset V) (z : V) (hz : z ∈ Z) :
    {τ // IsColoring q (identify F Z) τ} ≃
      {σ // IsColoring q F σ ∧ constantOn σ Z} where
  toFun τ := by
    refine ⟨fun v => τ.val (identifyVertex Z v), ?_⟩
    constructor
    · intro u v huv
      have hm : 0 < identify F Z s(identifyVertex Z u, identifyVertex Z v) := by
        apply (identify_pos_iff F Z _).2
        exact ⟨s(u, v), huv, by simp⟩
      exact τ.property (identifyVertex Z u) (identifyVertex Z v) hm
    · intro u hu v hv
      have hu' : identifyVertex Z u = none := by simp [identifyVertex, hu]
      have hv' : identifyVertex Z v = none := by simp [identifyVertex, hv]
      change τ.val (identifyVertex Z u) = τ.val (identifyVertex Z v)
      rw [hu', hv']
  invFun σ := by
    let ρ := quotientColoringFrom Z z σ.val
    refine ⟨ρ, ?_⟩
    intro x y hxy
    obtain ⟨d, hd, hdeq⟩ := (identify_pos_iff F Z (s(x, y))).1 hxy
    induction d using Sym2.ind with
    | h u v =>
      simp only [Sym2.map_mk] at hdeq
      rcases Sym2.eq_iff.mp hdeq with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · have hxu : ρ x = σ.val u := by
          rw [← hx]
          exact quotientColoringFrom_identifyVertex Z z hz σ.val σ.property.2 u
        have hyv : ρ y = σ.val v := by
          rw [← hy]
          exact quotientColoringFrom_identifyVertex Z z hz σ.val σ.property.2 v
        rw [hxu, hyv]
        exact σ.property.1 u v hd
      · have hyv : ρ x = σ.val v := by
          rw [← hy]
          exact quotientColoringFrom_identifyVertex Z z hz σ.val σ.property.2 v
        have hxu : ρ y = σ.val u := by
          rw [← hx]
          exact quotientColoringFrom_identifyVertex Z z hz σ.val σ.property.2 u
        rw [hyv, hxu]
        have hd' : 0 < F s(v, u) := by
          have hsym : s(u, v) = s(v, u) := Sym2.eq_swap
          rw [hsym] at hd
          exact hd
        exact σ.property.1 v u hd'
  left_inv τ := by
    apply Subtype.ext
    funext x
    cases x with
    | none =>
      simp [quotientColoringFrom, identifyVertex, hz]
    | some v =>
      simp [quotientColoringFrom, identifyVertex, v.property]
  right_inv σ := by
    apply Subtype.ext
    funext v
    exact quotientColoringFrom_identifyVertex Z z hz σ.val σ.property.2 v

theorem S5_04Statement_holds : ThLean.BP.S5.S5_04Statement := by
  intro V hV q hq F Z hZ
  obtain ⟨z, hz⟩ := hZ
  let E := identificationColoringEquiv q F Z z hz
  refine ⟨⟨E, ?_⟩, ?_, ?_⟩
  · intro τ
    rfl
  · constructor
    · rintro ⟨τ, hτ⟩
      exact ⟨(E ⟨τ, hτ⟩).val, (E ⟨τ, hτ⟩).property.1, (E ⟨τ, hτ⟩).property.2⟩
    · rintro ⟨σ, hσ, hconst⟩
      exact ⟨(E.symm ⟨σ, hσ, hconst⟩).val, (E.symm ⟨σ, hσ, hconst⟩).property⟩
  · rintro ⟨τ, hτ⟩
    exact ⟨(E ⟨τ, hτ⟩).val, (E ⟨τ, hτ⟩).property.1⟩

example : ThLean.BP.S5.S5_04Statement := S5_04Statement_holds

end ThLean.W.S564
