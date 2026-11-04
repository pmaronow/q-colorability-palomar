module

public import ThLean.BP.SA.Convergence

@[expose] public section

noncomputable section
open Filter
open scoped Topology
namespace ThLean.W.SA03
open ThLean.BP.SA
open ThresholdFoundations

theorem SA_C61bStatement_of_deps (hT39 : SA_T39Statement)
    (hpre : PreQuantileStatement) : SA_C61bStatement := by
  intro q hq Λ η K α δ n₁ hΛ hδ hη hη₀ hwindow hxi
  have hqreal : (1 : ℝ) < (q : ℝ) := by
    exact_mod_cast (show 1 < q by omega)
  have hqden : 0 < (q : ℝ) - 1 := by linarith
  have hratio : 1 < (q : ℝ) / ((q : ℝ) - 1) := by
    rw [lt_div_iff₀ hqden]
    nlinarith
  have hgamma : 0 < gamma q := by
    unfold gamma
    exact div_pos (Real.log_pos hqreal) (Real.log_pos hratio)
  have hΛpos : 0 < Λ := lt_trans (by linarith) hΛ
  have hetaHalf : η ≤ 1 / 2 := by
    have hexp : Real.exp (-2 * Λ) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    have heta : etaZero Λ < (1 / 8 : ℝ) := by
      unfold etaZero
      linarith
    exact le_trans hη₀ (by linarith)
  have hKpos : 0 < K := hwindow.1
  have hdelta := (hT39 Λ K δ hΛpos hKpos hδ).2.2
  have hKdelta : Tendsto (fun n : ℕ => K * δ n) atTop (𝓝 0) := by
    simpa using hdelta.const_mul K
  let err : ℕ → ℝ := fun n =>
    (upperLocation q Λ η n : ℝ) / n - xi q Λ η n
  have herr : Tendsto err atTop (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop (max (2 * q) n₁)] with n hn
      have hLleU := (hpre q n (cap Λ n) hq (by omega) η hη hetaHalf).1
      have hnpos : (0 : ℝ) < n := by
        exact_mod_cast (by omega : 0 < n)
      change 0 ≤ (upperLocation q Λ η n : ℝ) / n -
        (lowerLocation q Λ η n : ℝ) / n
      rw [← sub_div]
      exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hLleU)) hnpos.le
    · filter_upwards [eventually_ge_atTop (max (2 * q) n₁)] with n hn
      have hLleU := (hpre q n (cap Λ n) hq (by omega) η hη hetaHalf).1
      have hnposNat : 0 < n := by omega
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
      have hgap :
          (upperLocation q Λ η n : ℝ) - (lowerLocation q Λ η n : ℝ) ≤
            K * (n : ℝ) * δ n := by
        simpa [window] using hwindow.2 n hn
      have hgap' :
          (upperLocation q Λ η n : ℝ) - (lowerLocation q Λ η n : ℝ) ≤
            (K * δ n) * (n : ℝ) := by
        calc
          _ ≤ K * (n : ℝ) * δ n := hgap
          _ = (K * δ n) * (n : ℝ) := by ring
      have hdiv :
          ((upperLocation q Λ η n : ℝ) - (lowerLocation q Λ η n : ℝ)) / n ≤
            K * δ n := (div_le_iff₀ hnpos).2 hgap'
      change (upperLocation q Λ η n : ℝ) / n -
        (lowerLocation q Λ η n : ℝ) / n ≤ K * δ n
      rw [← sub_div]
      exact hdiv
    · exact hKdelta
  have hsum : Tendsto (fun n : ℕ => xi q Λ η n + err n) atTop (𝓝 α) := by
    simpa using hxi.add herr
  have heq :
      (fun n : ℕ => (upperLocation q Λ η n : ℝ) / n) =
        fun n => xi q Λ η n + err n := by
    funext n
    dsimp [err, xi]
    ring
  rw [heq]
  exact hsum

end ThLean.W.SA03
