import ThLean.BP.SA.Tree

noncomputable section

open Filter
open scoped BigOperators Topology ENNReal

namespace ThLean.W.SA62

open ThLean.BP.SA
open ThresholdFoundations

private def sample (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  g (Real.exp ((n : ℝ) + 1))

private def sampleTail (g : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑' k : ℕ, sample g (k + N)

private def pathConstant : ℝ :=
  ((Nat.ceil (1 / Real.log (4 / 3 : ℝ)) + 1 : ℕ) : ℝ)

private theorem sample_tail_tendsto {g : ℝ → ℝ} (hs : Summable (sample g)) :
    Tendsto (sampleTail g) atTop (𝓝 0) := by
  have hp := hs.hasSum.tendsto_sum_nat
  have hp' : Tendsto (fun N => (∑' n : ℕ, sample g n) -
      ∑ n ∈ Finset.range N, sample g n) atTop (𝓝 0) := by
    convert tendsto_const_nhds.sub hp using 1
    simp
  have hEq : sampleTail g = fun N => (∑' n : ℕ, sample g n) -
      ∑ n ∈ Finset.range N, sample g n := by
    funext N
    have hdecomp := hs.sum_add_tsum_nat_add N
    unfold sampleTail
    linarith
  rw [hEq]
  exact hp'

private theorem sample_arg_tendsto :
    Tendsto (fun n : ℕ => Real.exp ((n : ℝ) + 1)) atTop atTop := by
  apply Real.tendsto_exp_atTop.comp
  exact (tendsto_natCast_atTop_atTop).atTop_add tendsto_const_nhds

private theorem gridTail_tendsto {u₀ : ℝ} {g : ℝ → ℝ}
    (hg : AnalyticError u₀ g) :
    Tendsto (fun K : ℕ => ∑' k : ℕ,
      g (Real.exp ((K + 1 + k : ℕ) : ℝ))) atTop (𝓝 0) := by
  have hs : Summable (sample g) := by
    exact hg.2.2.2
  have ht := sample_tail_tendsto (g := g) hs
  have hEq : (fun K : ℕ => ∑' k : ℕ,
      g (Real.exp ((K + 1 + k : ℕ) : ℝ))) = sampleTail g := by
    funext K
    apply tsum_congr
    intro k
    change g (Real.exp ((K + 1 + k : ℕ) : ℝ)) =
      g (Real.exp (((k + K : ℕ) : ℝ) + 1))
    congr 2
    push_cast
    ring
  rw [hEq]
  exact ht

private theorem path_bound
    (h35 : SA_T35Statement) {u₀ : ℝ} {g : ℝ → ℝ}
    (hg : AnalyticError u₀ g) (K : ℕ) (hK : u₀ ≤ Real.exp K)
    (ℓ : ℝ) (hℓ : 4 * Real.exp K ≤ ℓ) :
    Summable (fun i : ℕ => g (ℓ / 4 * (4 / 3 : ℝ) ^ (i + 1))) ∧
      0 ≤ pathError g ℓ ∧
      pathError g ℓ ≤ pathConstant *
        ∑' k : ℕ, g (Real.exp ((K + k : ℕ) : ℝ)) := by
  let f : ℕ → ℝ := fun i => g (ℓ / 4 * (4 / 3 : ℝ) ^ (i + 1))
  have hterm : ∀ i, 0 ≤ f i := by
    intro i
    apply hg.2.1
    have hexp : 1 ≤ Real.exp (K : ℝ) := by
      have h := Real.add_one_le_exp (K : ℝ)
      have hk : 0 ≤ (K : ℝ) := by positivity
      linarith
    have hpow : 1 ≤ (4 / 3 : ℝ) ^ (i + 1) :=
      one_le_pow₀ (by norm_num : 1 ≤ (4 / 3 : ℝ))
    have hbase : Real.exp (K : ℝ) ≤ ℓ / 4 := by
      nlinarith [hℓ]
    have hmul : ℓ / 4 ≤ ℓ / 4 * (4 / 3 : ℝ) ^ (i + 1) := by
      have hnonneg : 0 ≤ ℓ / 4 := by linarith [Real.exp_pos (K : ℝ)]
      nlinarith
    have hu : u₀ ≤ ℓ / 4 * (4 / 3 : ℝ) ^ (i + 1) :=
      hK.trans (hbase.trans hmul)
    exact le_trans hg.1 hu
  have hpartial : ∀ m, ∑ i ∈ Finset.range m, f i ≤
      pathConstant * ∑' k : ℕ, g (Real.exp ((K + k : ℕ) : ℝ)) := by
    intro m
    simpa [f, pathConstant] using h35 u₀ g hg K hK ℓ hℓ m
  have hs : Summable f := summable_of_sum_range_le hterm hpartial
  have hsum : pathError g ℓ ≤
      pathConstant * ∑' k : ℕ, g (Real.exp ((K + k : ℕ) : ℝ)) := by
    simpa [pathError, f] using hs.tsum_le_of_sum_range_le hpartial
  exact ⟨by simpa [f], tsum_nonneg hterm, hsum⟩

private theorem path_summable
    (h35 : SA_T35Statement) {u₀ : ℝ} {g : ℝ → ℝ}
    (hg : AnalyticError u₀ g) (ℓ : ℝ) (hℓ : 4 * u₀ ≤ ℓ) :
    Summable (fun i : ℕ => g (ℓ / 4 * (4 / 3 : ℝ) ^ (i + 1))) := by
  have hexp := sample_arg_tendsto
  obtain ⟨K, hK⟩ := (tendsto_atTop.1 hexp u₀).exists
  have hbase : Tendsto (fun n : ℕ => (4 / 3 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hℓpos : 0 < ℓ := by
    have hu : 0 < u₀ := lt_of_lt_of_le (by norm_num) hg.1
    linarith
  have hparam : Tendsto (fun n : ℕ => ℓ * (4 / 3 : ℝ) ^ n) atTop atTop := by
    simpa [mul_comm] using hbase.atTop_mul_const hℓpos
  obtain ⟨N, hN⟩ := (tendsto_atTop.1 hparam (4 * Real.exp ((K : ℝ) + 1))).exists
  have hN' : 4 * Real.exp ((K : ℝ) + 1) ≤ ℓ * (4 / 3 : ℝ) ^ N := hN
  have hK' : u₀ ≤ Real.exp ((K + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add] using hK
  have hN'' : 4 * Real.exp ((K + 1 : ℕ) : ℝ) ≤ ℓ * (4 / 3 : ℝ) ^ N := by
    simpa [Nat.cast_add] using hN'
  have htail := path_bound h35 hg (K + 1) hK' (ℓ * (4 / 3 : ℝ) ^ N) hN''
  have htailSummable : Summable (fun i : ℕ =>
      g ((ℓ * (4 / 3 : ℝ) ^ N) / 4 * (4 / 3 : ℝ) ^ (i + 1))) := htail.1
  have hshift : Summable (fun i : ℕ =>
      g (ℓ / 4 * (4 / 3 : ℝ) ^ ((i + N) + 1))) := by
    have hfun : (fun i : ℕ =>
        g (ℓ / 4 * (4 / 3 : ℝ) ^ ((i + N) + 1))) =
        (fun i : ℕ =>
        g ((ℓ * (4 / 3 : ℝ) ^ N) / 4 * (4 / 3 : ℝ) ^ (i + 1))) := by
      funext i
      apply congrArg g
      calc
        ℓ / 4 * (4 / 3 : ℝ) ^ ((i + N) + 1)
            = ℓ / 4 * ((4 / 3 : ℝ) ^ N * (4 / 3 : ℝ) ^ (i + 1)) := by
                rw [show (i + N) + 1 = N + (i + 1) by omega, pow_add]
        _ = (ℓ * (4 / 3 : ℝ) ^ N) / 4 * (4 / 3 : ℝ) ^ (i + 1) := by ring
    exact hfun ▸ htailSummable
  have hnat : Summable (fun i : ℕ =>
      g (ℓ / 4 * (4 / 3 : ℝ) ^ (i + 1))) :=
    (summable_nat_add_iff N).mp hshift
  simpa using hnat

theorem SA_T36Statement_of_deps (h35 : SA_T35Statement) : SA_T36Statement := by
  intro u₀ g hg
  have hsample : Summable (sample g) := by
    exact hg.2.2.2
  have hsample_zero : Tendsto (sample g) atTop (𝓝 0) := hsample.tendsto_atTop_zero
  have harg := sample_arg_tendsto
  have hgz : Tendsto g atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨N₀, hNsmall⟩ := Metric.tendsto_atTop.1 hsample_zero ε hε
    obtain ⟨N₁, hNlarge⟩ := eventually_atTop.1 (tendsto_atTop.1 harg u₀)
    let N := max N₀ N₁
    refine ⟨Real.exp ((N : ℝ) + 1), ?_⟩
    intro x hx
    have hNsmall' := hNsmall N (le_max_left _ _)
    have hNlarge' := hNlarge N (le_max_right _ _)
    have hy : u₀ ≤ Real.exp ((N : ℝ) + 1) := hNlarge'
    have hxU : u₀ ≤ x := hy.trans hx
    have hanti := hg.2.2.1
    have hle : g x ≤ g (Real.exp ((N : ℝ) + 1)) :=
      hanti (Set.mem_Ici.mpr hy) (Set.mem_Ici.mpr hxU) hx
    have hnon : 0 ≤ g x := hg.2.1 x (le_trans hg.1 hxU)
    have hysample : 0 ≤ g (Real.exp ((N : ℝ) + 1)) :=
      hg.2.1 _ (le_trans hg.1 hy)
    have hdistL : dist (g x) 0 = g x := by
      simp [abs_of_nonneg hnon]
    have hdistR : dist (sample g N) 0 = g (Real.exp ((N : ℝ) + 1)) := by
      simp [sample, abs_of_nonneg hysample]
    have hdist : dist (g x) 0 ≤ dist (sample g N) 0 := by
      rw [hdistL, hdistR]
      exact hle
    exact hdist.trans_lt hNsmall'
  have hsmallTail : Tendsto (fun K : ℕ => pathConstant *
      (∑' k : ℕ, g (Real.exp ((K + 1 + k : ℕ) : ℝ)))) atTop (𝓝 0) := by
    simpa using (gridTail_tendsto hg).const_mul pathConstant
  have hRzero : Tendsto (pathError g) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨K₀, hKsmall⟩ := Metric.tendsto_atTop.1 hsmallTail ε hε
    obtain ⟨K₁, hKcut⟩ := eventually_atTop.1 (tendsto_atTop.1 harg u₀)
    let K := max K₀ K₁
    have hKsmall' := hKsmall K (le_max_left _ _)
    have hKcut' := hKcut K (le_max_right _ _)
    let cutoff : ℝ := 4 * Real.exp ((K : ℝ) + 1)
    refine ⟨cutoff, ?_⟩
    intro ℓ hℓ
    have hKcutNat : u₀ ≤ Real.exp ((K + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add] using hKcut'
    have hb := path_bound h35 hg (K + 1) hKcutNat ℓ (by simpa [cutoff] using hℓ)
    have hconstant : 0 ≤ pathConstant := by
      unfold pathConstant
      positivity
    have hgrid : 0 ≤ ∑' k : ℕ,
        g (Real.exp ((K + 1 + k : ℕ) : ℝ)) := by
      apply tsum_nonneg
      intro k
      apply hg.2.1
      have harg' : u₀ ≤ Real.exp ((K + 1 + k : ℕ) : ℝ) := by
        apply hKcutNat.trans
        apply Real.exp_le_exp.mpr
        exact_mod_cast Nat.le_add_right (K + 1) k
      exact le_trans hg.1 harg'
    have hrhs : 0 ≤ pathConstant * (∑' k : ℕ,
        g (Real.exp ((K + 1 + k : ℕ) : ℝ))) := mul_nonneg hconstant hgrid
    have hleft : dist (pathError g ℓ) 0 = pathError g ℓ := by
      simp [abs_of_nonneg hb.2.1]
    have hright : dist (pathConstant * (∑' k : ℕ,
        g (Real.exp ((K + 1 + k : ℕ) : ℝ)))) 0 =
        pathConstant * (∑' k : ℕ,
          g (Real.exp ((K + 1 + k : ℕ) : ℝ))) := by
      calc
        _ = |pathConstant * (∑' k : ℕ,
            g (Real.exp ((K + 1 + k : ℕ) : ℝ)))| := by simp
        _ = pathConstant * (∑' k : ℕ,
            g (Real.exp ((K + 1 + k : ℕ) : ℝ))) := by
              rw [abs_mul, abs_of_nonneg hconstant, abs_of_nonneg hgrid]
    have hdist : dist (pathError g ℓ) 0 ≤
        dist (pathConstant * (∑' k : ℕ,
          g (Real.exp ((K + 1 + k : ℕ) : ℝ)))) 0 := by
      rw [hleft, hright]
      exact hb.2.2
    exact hdist.trans_lt hKsmall'
  refine ⟨?_, ?_, hgz, hRzero⟩
  · intro ℓ hℓ
    have hs := path_summable h35 hg ℓ hℓ
    have hnon : ∀ i : ℕ, 0 ≤ g (ℓ / 4 * (4 / 3 : ℝ) ^ (i + 1)) := by
      intro i
      apply hg.2.1
      have hpow : 1 ≤ (4 / 3 : ℝ) ^ (i + 1) :=
        one_le_pow₀ (by norm_num : 1 ≤ (4 / 3 : ℝ))
      have hbase : u₀ ≤ ℓ / 4 := by nlinarith [hℓ]
      have hmul : ℓ / 4 ≤ ℓ / 4 * (4 / 3 : ℝ) ^ (i + 1) := by
        have hℓnon : 0 ≤ ℓ / 4 := by nlinarith [hℓ, hg.1]
        nlinarith
      exact le_trans (le_trans hg.1 hbase) hmul
    exact ⟨hs, tsum_nonneg hnon⟩
  · intro K hK ℓ hℓ
    exact (path_bound h35 hg K hK ℓ hℓ).2.2

end ThLean.W.SA62
