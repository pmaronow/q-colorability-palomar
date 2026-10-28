import ThLean.BP.S5.Poisson

noncomputable section
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S559S
open ThresholdFoundations ThLean.BP.S5

lemma uniformMean_range {A : Type*} [Fintype A] (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    0 ≤ uniformMean f ∧ uniformMean f ≤ 1 := by
  unfold uniformMean
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun a _ => (hf a).1) (Nat.cast_nonneg _)
  · by_cases h : Fintype.card A = 0
    · simp [h]
    · have hp : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
      apply (div_le_iff₀ hp).2
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun a _ => (hf a).2)

lemma indicator_range (P : Prop) : 0 ≤ indicator P ∧ indicator P ≤ 1 := by
  by_cases h : P <;> simp [indicator, h]

lemma pair_nonempty {V : Type} [Fintype V] (hV : 2 ≤ Fintype.card V) :
    Nonempty (Pair V) := by
  have hex : ∃ a b : V, a ≠ b := by
    by_contra h
    have hcard : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.mpr (by aesop)
    omega
  obtain ⟨a, b, hab⟩ := hex
  refine ⟨⟨s(a, b), ?_⟩⟩
  intro v hv
  rcases Sym2.eq_iff.mp hv with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> subst_vars <;> exact hab rfl

lemma countMean_eq_graphMean (h08 : S5_08BStatement)
    {V : Type} [Fintype V] (hV : 2 ≤ Fintype.card V)
    (r : ℝ) (hr : 0 ≤ r) (f : MGraph V → ℝ)
    (hf : ∃ C : ℝ, ∀ G, |f G| ≤ C) :
    countMean r f = poissonGraphMean (r * ((Fintype.card V).choose 2 : ℝ)) f := by
  have hc : ((Fintype.card V).choose 2 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hV)
  have h := h08 V hV (r * ((Fintype.card V).choose 2 : ℝ)) (by positivity) f hf
  rw [mul_div_cancel_right₀ r hc] at h
  exact h.symm

abbrev graphMass {V : Type} [Fintype V] (r : ℝ) (G : MGraph V) : ℝ :=
  independentPoissonGraphMass (perPairRate r) G

lemma graphMass_nonneg {V : Type} [Fintype V] {r : ℝ} (hr : 0 ≤ r)
    (G : MGraph V) : 0 ≤ graphMass r G := by
  apply Finset.prod_nonneg
  intro e _
  unfold poissonWeight perPairRate
  split_ifs <;> positivity

lemma graphMass_hasSum (h08 : S5_08BStatement) (hE01 : S5_E01Statement)
    {V : Type} [Fintype V] (hV : 2 ≤ Fintype.card V)
    (r : ℝ) (hr : 0 ≤ r) : HasSum (graphMass (V := V) r) 1 := by
  have : Nonempty (Pair V) := pair_nonempty hV
  have hc := countMean_eq_graphMean h08 hV r hr (fun _ => 1) ⟨1, by simp⟩
  have htuple : ∀ m, uniformMean (fun _ : EdgeTuple V m => (1 : ℝ)) = 1 := by
    intro m
    simp [uniformMean]
  have ht : 0 ≤ r * ((Fintype.card V).choose 2 : ℝ) := by positivity
  have hpg : poissonGraphMean (r * ((Fintype.card V).choose 2 : ℝ))
      (fun _ : MGraph V => 1) = 1 := by
    simpa only [poissonGraphMean, poissonMixture, htuple, mul_one] using
      (hE01.1 _ ht).2.1.tsum_eq
  have heq : (∑' G : MGraph V, graphMass r G) = 1 := by
    simpa [countMean, independentPoissonGraphMean] using hc.trans hpg
  have hs : Summable (graphMass (V := V) r) := by
    by_contra h
    have := tsum_eq_zero_of_not_summable h
    rw [heq] at this
    norm_num at this
  exact heq ▸ hs.hasSum

def countPMF (h08 : S5_08BStatement) (hE01 : S5_E01Statement)
    {V : Type} [Fintype V] (hV : 2 ≤ Fintype.card V)
    (r : ℝ) (hr : 0 ≤ r) : PMF (MGraph V) :=
  ⟨fun G => ENNReal.ofReal (graphMass r G), by
    apply ENNReal.summable.hasSum_iff.mpr
    rw [← ENNReal.ofReal_tsum_of_nonneg (graphMass_nonneg hr)
      (graphMass_hasSum h08 hE01 hV r hr).summable,
      (graphMass_hasSum h08 hE01 hV r hr).tsum_eq]
    simp⟩

lemma lawMean_countPMF (h08 : S5_08BStatement) (hE01 : S5_E01Statement)
    {V : Type} [Fintype V] (hV : 2 ≤ Fintype.card V)
    (r : ℝ) (hr : 0 ≤ r) (f : MGraph V → ℝ) :
    lawMean (countPMF h08 hE01 hV r hr) f = countMean r f := by
  unfold lawMean countMean independentPoissonGraphMean
  apply tsum_congr
  intro G
  change (ENNReal.ofReal (graphMass r G)).toReal * f G = graphMass r G * f G
  rw [ENNReal.toReal_ofReal (graphMass_nonneg hr G)]

def pairPerm {V : Type} (π : Equiv.Perm V) : Equiv.Perm (Sym2 V) where
  toFun := Sym2.map π
  invFun := Sym2.map π.symm
  left_inv e := by
    induction e using Sym2.ind with | _ a b => simp
  right_inv e := by
    induction e using Sym2.ind with | _ a b => simp

def graphPerm {V : Type} (π : Equiv.Perm V) : Equiv.Perm (MGraph V) where
  toFun G e := G ((pairPerm π).symm e)
  invFun G e := G (pairPerm π e)
  left_inv G := by funext e; simp
  right_inv G := by funext e; simp

lemma relabel_eq_graphPerm {V : Type} [Fintype V] (π : Equiv.Perm V)
    (G : MGraph V) : relabel π G = graphPerm π G := by
  funext e
  unfold relabel mapGraph
  rw [Finset.sum_eq_single ((pairPerm π).symm e)]
  · change (if (pairPerm π) ((pairPerm π).symm e) = e
        then G ((pairPerm π).symm e) else 0) = G ((pairPerm π).symm e)
    rw [(pairPerm π).apply_symm_apply]
    simp
  · intro b _ hne
    have hnot : Sym2.map π b ≠ e := by
      intro h
      exact hne ((pairPerm π).injective (h.trans ((pairPerm π).apply_symm_apply e).symm))
    simp [hnot]
  · simp

lemma perPairRate_perm {V : Type} (π : Equiv.Perm V) (r : ℝ) (e : Sym2 V) :
    perPairRate r (pairPerm π e) = perPairRate r e := by
  have hdiag : (∃ v, pairPerm π e = s(v, v)) ↔ ∃ v, e = s(v, v) := by
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨π.symm v, ?_⟩
      have h := congrArg (pairPerm π).symm hv
      rw [(pairPerm π).symm_apply_apply] at h
      exact h
    · rintro ⟨v, rfl⟩
      exact ⟨π v, rfl⟩
  simp only [perPairRate, hdiag]

lemma graphMass_perm {V : Type} [Fintype V] (π : Equiv.Perm V)
    (r : ℝ) (G : MGraph V) : graphMass r (graphPerm π G) = graphMass r G := by
  unfold graphMass independentPoissonGraphMass
  rw [← Equiv.prod_comp (pairPerm π)]
  apply Finset.prod_congr rfl
  intro e _
  simp only [perPairRate_perm]
  congr 1
  change G ((pairPerm π).symm (pairPerm π e)) = G e
  rw [(pairPerm π).symm_apply_apply]

lemma countPMF_invariant (h08 : S5_08BStatement) (hE01 : S5_E01Statement)
    {V : Type} [Fintype V] (hV : 2 ≤ Fintype.card V)
    (r : ℝ) (hr : 0 ≤ r) : invariantLaw (countPMF h08 hE01 hV r hr) := by
  intro π
  apply PMF.ext
  intro G
  rw [PMF.map_apply]
  simp_rw [relabel_eq_graphPerm]
  rw [tsum_eq_single ((graphPerm π).symm G)]
  · simp only [(graphPerm π).apply_symm_apply, ite_true]
    change ENNReal.ofReal (graphMass r ((graphPerm π).symm G)) = ENNReal.ofReal (graphMass r G)
    congr 1
    have h := graphMass_perm π r ((graphPerm π).symm G)
    simpa using h.symm
  · intro B hne
    have hnot : G ≠ graphPerm π B := by
      intro h
      apply hne
      exact (graphPerm π).injective (h.symm.trans ((graphPerm π).apply_symm_apply G).symm)
    simp [hnot]

end ThLean.W.S559S
