module

public import ThLean.BP.S5.Structure

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S567
open ThresholdFoundations

private theorem identify_subgraph_of_subgraph
    {V : Type} [Fintype V] (F F' : MGraph V) (Z : Finset V)
    (hFF' : subgraph F F') : subgraph (identify F Z) (identify F' Z) := by
  intro e
  unfold identify mapGraph
  apply Finset.sum_le_sum
  intro d hd
  split_ifs
  · exact hFF' d
  · exact Nat.zero_le _

private theorem mapGraph_edge_pos
    {V W : Type} [Fintype V] [Fintype W]
    (f : V → W) (F : MGraph V) {u v : V}
    (h : 0 < F (s(u, v))) :
    0 < mapGraph f F (s(f u, f v)) := by
  unfold mapGraph
  apply lt_of_lt_of_le h
  calc
    F (s(u, v)) = (if Sym2.map f (s(u, v)) = s(f u, f v) then F (s(u, v)) else 0) := by simp
    _ ≤ ∑ e, if Sym2.map f e = s(f u, f v) then F e else 0 :=
      Finset.single_le_sum
        (f := fun e => if Sym2.map f e = s(f u, f v) then F e else 0)
        (fun e he => Nat.zero_le _) (Finset.mem_univ _)

private theorem mapGraph_edge_preimage
    {V W : Type} [Fintype V] [Fintype W]
    (f : V → W) (F : MGraph V) {e : Sym2 W}
    (h : 0 < mapGraph f F e) :
    ∃ a b, 0 < F (s(a, b)) ∧ Sym2.map f (s(a, b)) = e := by
  unfold mapGraph at h
  have hex : ∃ d, Sym2.map f d = e ∧ 0 < F d := by
    by_contra hn
    have hz : ∀ d, (if Sym2.map f d = e then F d else 0) = 0 := by
      intro d
      by_cases hd : Sym2.map f d = e
      · have hnot : ¬ 0 < F d := fun hp => hn ⟨d, hd, hp⟩
        simp [hd, Nat.eq_zero_of_not_pos hnot]
      · simp [hd]
    have hsum : (∑ d, if Sym2.map f d = e then F d else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      exact hz d
    omega
  obtain ⟨d, hde, hFd⟩ := hex
  induction d using Sym2.inductionOn with
  | hf a b =>
      exact ⟨a, b, by simpa using hFd, by simpa only [Sym2.map_mk] using hde⟩

private theorem identify_colorable_iff_constant
    {V : Type} [Fintype V] (q : ℕ) (F : MGraph V) (Z : Finset V)
    (hZ : Z.Nonempty) :
    Colorable q (identify F Z) ↔
      ∃ σ, IsColoring q F σ ∧ constantOn σ Z := by
  constructor
  · rintro ⟨τ, hτ⟩
    let σ : V → Fin q := fun v => τ (identifyVertex Z v)
    refine ⟨σ, ?_, ?_⟩
    · intro u v huv
      exact hτ (identifyVertex Z u) (identifyVertex Z v)
        (mapGraph_edge_pos (identifyVertex Z) F huv)
    · intro u hu v hv
      simp [σ, identifyVertex, hu, hv]
  · rintro ⟨σ, hσ, hconst⟩
    obtain ⟨z₀, hz₀⟩ := hZ
    let τ : QuotientVertices Z → Fin q := fun w =>
      match w with
      | none => σ z₀
      | some v => σ v.val
    have hfactor : ∀ v, τ (identifyVertex Z v) = σ v := by
      intro v
      by_cases hv : v ∈ Z
      · simpa [τ, identifyVertex, hv] using (hconst v hv z₀ hz₀).symm
      · simp [τ, identifyVertex, hv]
    refine ⟨τ, ?_⟩
    intro u v huv
    obtain ⟨a, b, hab, heq⟩ := mapGraph_edge_preimage (identifyVertex Z) F huv
    have hab' : τ (identifyVertex Z a) ≠ τ (identifyVertex Z b) := by
      simpa [hfactor a, hfactor b] using hσ a b hab
    have heq' : s(identifyVertex Z a, identifyVertex Z b) = s(u, v) := by
      simpa only [Sym2.map_mk] using heq
    rcases Sym2.eq_iff.mp heq' with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
    · rw [← hau, ← hbv]
      exact hab'
    · rw [← hbu, ← hav]
      exact hab'.symm

private theorem list_image_card_ge_two_iff_not_constant
    {V : Type} [Fintype V] (q : ℕ) (xs : List V) (σ : V → Fin q) :
    2 ≤ (xs.map σ).toFinset.card ↔ ¬ constantOn σ xs.toFinset := by
  classical
  constructor
  · intro hcard hconst
    have hle : (xs.map σ).toFinset.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      rcases List.mem_map.mp (List.mem_toFinset.mp ha) with ⟨u, hu, rfl⟩
      rcases List.mem_map.mp (List.mem_toFinset.mp hb) with ⟨v, hv, rfl⟩
      exact hconst u (List.mem_toFinset.mpr hu) v (List.mem_toFinset.mpr hv)
    omega
  · intro hnot
    have hpair : ∃ a ∈ (xs.map σ).toFinset, ∃ b ∈ (xs.map σ).toFinset, a ≠ b := by
      by_contra hn
      apply hnot
      intro u hu v hv
      have hmemu : σ u ∈ (xs.map σ).toFinset :=
        List.mem_toFinset.mpr (List.mem_map.mpr ⟨u, List.mem_toFinset.mp hu, rfl⟩)
      have hmemv : σ v ∈ (xs.map σ).toFinset :=
        List.mem_toFinset.mpr (List.mem_map.mpr ⟨v, List.mem_toFinset.mp hv, rfl⟩)
      by_contra hne
      exact hn ⟨σ u, hmemu, σ v, hmemv, hne⟩
    have : 1 < (xs.map σ).toFinset.card := Finset.one_lt_card.mpr hpair
    omega

private theorem list_toFinset_nonempty_of_ne_nil
    {V : Type} [DecidableEq V] (xs : List V) (hxs : xs ≠ []) : xs.toFinset.Nonempty := by
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons x xs => exact ⟨x, by simp⟩

open ThLean.BP.S5

theorem S5_05Statement_holds : ThLean.BP.S5.S5_05Statement := by
  intro V hV q hq
  refine ⟨?_, ?_, ?_⟩
  · intro F F' Z hZ hFF'
    have hmono : subgraph (identify F Z) (identify F' Z) :=
      identify_subgraph_of_subgraph F F' Z hFF'
    refine ⟨hmono, ?_⟩
    intro hnot hcol
    apply hnot
    obtain ⟨σ, hσ⟩ := hcol
    refine ⟨σ, ?_⟩
    intro u v huv
    exact hσ u v (lt_of_lt_of_le huv (hmono (s(u, v))))
  · intro F xs hF hxs
    constructor
    · intro hnm hcol
      obtain ⟨σ, hσ, hconst⟩ :=
        (identify_colorable_iff_constant q F xs.toFinset
          (list_toFinset_nonempty_of_ne_nil xs hxs)).mp hcol
      have hcard := (hnm.2 σ hσ)
      exact (list_image_card_ge_two_iff_not_constant q xs σ).mp hcard hconst
    · intro hnot
      refine ⟨hF, ?_⟩
      intro σ hσ
      apply (list_image_card_ge_two_iff_not_constant q xs σ).mpr
      intro hconst
      apply hnot
      exact (identify_colorable_iff_constant q F xs.toFinset
        (list_toFinset_nonempty_of_ne_nil xs hxs)).mpr ⟨σ, hσ, hconst⟩
  · intro F xs Z hnm hsubset hZ
    have hno : ¬ Colorable q (identify F Z) := by
      intro hc
      obtain ⟨σ, hσ, hconst⟩ := (identify_colorable_iff_constant q F Z hZ).mp hc
      have hnotconst : ¬ constantOn σ xs.toFinset :=
        (list_image_card_ge_two_iff_not_constant q xs σ).mp (hnm.2 σ hσ)
      apply hnotconst
      intro u hu v hv
      exact hconst u (hsubset hu) v (hsubset hv)
    exact hno

end ThLean.W.S567
