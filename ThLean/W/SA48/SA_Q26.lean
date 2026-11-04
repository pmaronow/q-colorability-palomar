module

public import ThLean.BP.SA.Convergence

@[expose] public section

set_option maxHeartbeats 1000000
noncomputable section
open Set
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.SA48
open ThresholdFoundations
open ThLean.BP.SA

theorem SA_Q26Statement_of_deps
    (hI13b : SA_I13bStatement)
    (hI16b : SA_I16bStatement)
    (hI16c : SA_I16cStatement)
    (hQ22a : SA_Q22aStatement)
    (hQ25 : SA_Q25Statement)
    (hQ23a : SA_Q23aStatement)
    (hQ23b : SA_Q23bStatement)
    (hF01 : SA_F01Statement)
    (hC60a : SA_C60aStatement) : SA_Q26Statement := by
  intro q hq Λ η K δ n₁ s₀ hΛ hδ hη hη₀ hw hcut a b ha hb
  let N : ℕ := a + b
  let u : ℕ := min a b
  let c : ℝ := min
    (xi q Λ η a - 2 * (poissonDeviation a : ℝ) / a)
    (xi q Λ η b - 2 * (poissonDeviation b : ℝ) / b)

  have hparams := (hF01 q hq).2.2 Λ hΛ
  have hΛpos := hparams.1
  have hηZeroLt := hparams.2.2.1
  have hηSmall : η < 1 / 8 := lt_of_le_of_lt hη₀ hηZeroLt
  have hηHalf : η ≤ 1 / 2 := by linarith
  have hKpos := hw.1

  have hbase : max (2 * q) n₁ ≤ s₀ :=
    le_trans (le_max_left _ _) hcut.1
  have hceil : Nat.ceil (Real.exp 2) ≤ s₀ :=
    le_trans (le_max_right _ _) hcut.1
  have hs0exp : Real.exp 2 ≤ (s₀ : ℝ) := by
    calc
      Real.exp 2 ≤ (Nat.ceil (Real.exp 2) : ℝ) := Nat.le_ceil _
      _ ≤ s₀ := by exact_mod_cast hceil
  have hs0n₁ : n₁ ≤ s₀ := le_trans (le_max_right _ _) hbase
  have hmaxa : max (2 * q) n₁ ≤ a := le_trans hbase ha
  have hmaxb : max (2 * q) n₁ ≤ b := le_trans hbase hb
  have hqa : 2 * q ≤ a := le_trans (le_max_left _ _) hmaxa
  have hqb : 2 * q ≤ b := le_trans (le_max_left _ _) hmaxb
  have hua : u ≤ a := by dsimp [u]; exact Nat.min_le_left _ _
  have hub : u ≤ b := by dsimp [u]; exact Nat.min_le_right _ _
  have hus : s₀ ≤ u := by dsimp [u]; omega
  have huN : u ≤ N := by dsimp [u, N]; omega
  have hNq : 2 * q ≤ N := by dsimp [N]; omega
  have hNcut : s₀ ≤ N := le_trans ha (by dsimp [N]; omega)
  have hN₁ : n₁ ≤ N := le_trans hs0n₁ hNcut
  have huPos : 1 ≤ u := by omega
  have haPos : 1 ≤ a := by omega
  have hbPos : 1 ≤ b := by omega
  have hNPos : 1 ≤ N := by omega
  have huExp : Real.exp 2 ≤ (u : ℝ) := by
    calc
      Real.exp 2 ≤ (s₀ : ℝ) := hs0exp
      _ ≤ u := by exact_mod_cast hus
  have haExp : Real.exp 2 ≤ (a : ℝ) := le_trans huExp (by exact_mod_cast hua)
  have hbExp : Real.exp 2 ≤ (b : ℝ) := le_trans huExp (by exact_mod_cast hub)
  have hNExp : Real.exp 2 ≤ (N : ℝ) := le_trans huExp (by exact_mod_cast huN)

  rcases hcut.2 a ha with ⟨hupperA, hxiA, hsmallA, htailA⟩
  rcases hcut.2 b hb with ⟨hupperB, hxiB, hsmallB, htailB⟩
  rcases hcut.2 N hNcut with ⟨hupperN, hxiNcut, hsmallN, htailN⟩

  have hxiBoundA := hC60a q hq Λ η hΛ hη hηHalf a hqa
  have hxiBoundB := hC60a q hq Λ η hΛ hη hηHalf b hqb
  have hxiALe : xi q Λ η a ≤ Λ := hxiBoundA.2
  have hxiBLe : xi q Λ η b ≤ Λ := hxiBoundB.2

  have hcA : 0 < xi q Λ η a - 2 * (poissonDeviation a : ℝ) / a := by
    linarith [hxiA, hsmallA]
  have hcB : 0 < xi q Λ η b - 2 * (poissonDeviation b : ℝ) / b := by
    linarith [hxiB, hsmallB]
  have hcPos : 0 < c := by
    dsimp [c]
    exact lt_min hcA hcB
  have hcLeA : c ≤ xi q Λ η a - 2 * (poissonDeviation a : ℝ) / a := by
    dsimp [c]
    exact min_le_left _ _
  have hcLeB : c ≤ xi q Λ η b - 2 * (poissonDeviation b : ℝ) / b := by
    dsimp [c]
    exact min_le_right _ _
  have hdevA0 : 0 ≤ (poissonDeviation a : ℝ) / a :=
    div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hbaseA : xi q Λ η a - 2 * (poissonDeviation a : ℝ) / a ≤ xi q Λ η a := by
    have hnum : 0 ≤ 2 * (poissonDeviation a : ℝ) :=
      mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    have htwice : 0 ≤ (2 * (poissonDeviation a : ℝ)) / a :=
      div_nonneg hnum (by positivity)
    linarith
  have hcLeΛ : c ≤ Λ := le_trans (le_trans hcLeA hbaseA) hxiALe

  have hrate : ∀ n : ℕ, 2 * q ≤ n →
      c ≤ xi q Λ η n - 2 * (poissonDeviation n : ℝ) / n →
      c * ((n : ℝ) - 1) ≤ (lowerLocation q Λ η n : ℝ) - poissonDeviation n := by
    intro n hqn hcxi
    have hn : 1 ≤ n := by omega
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hcn : c * ((n : ℝ) - 1) ≤ c * n := by
      have hc0 : 0 ≤ c := hcPos.le
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcxi (show 0 ≤ (n : ℝ) by positivity)
    have hmul' : c * (n : ℝ) ≤ (lowerLocation q Λ η n : ℝ) -
        2 * (poissonDeviation n : ℝ) := by
      calc
        c * (n : ℝ) ≤ (xi q Λ η n - 2 * (poissonDeviation n : ℝ) / n) * n := hmul
        _ = (lowerLocation q Λ η n : ℝ) - 2 * (poissonDeviation n : ℝ) := by
          rw [xi]
          field_simp [ne_of_gt hnR]
    have hdev0 : 0 ≤ (poissonDeviation n : ℝ) := Nat.cast_nonneg _
    calc
      c * ((n : ℝ) - 1) ≤ c * n := hcn
      _ ≤ (lowerLocation q Λ η n : ℝ) - 2 * (poissonDeviation n : ℝ) := hmul'
      _ ≤ (lowerLocation q Λ η n : ℝ) - poissonDeviation n := by linarith

  have hrateA := hrate a hqa hcLeA
  have hrateB := hrate b hqb hcLeB
  have hηA : η ≤ 1 / 2 := hηHalf
  have htailηA : poissonTailError Λ a ≤ η := le_trans htailA (min_le_left _ _)
  have htailηB : poissonTailError Λ b ≤ η := le_trans htailB (min_le_left _ _)
  have htailηN : poissonTailError Λ N ≤ η := le_trans htailN (min_le_left _ _)
  have hρA := hQ22a q a hq hqa Λ η c hΛ hη hηA hcPos hcLeΛ hrateA
  have hρB := hQ22a q b hq hqb Λ η c hΛ hη hηA hcPos hcLeΛ hrateB

  have hη8 : η ≤ 1 / 8 := le_of_lt hηSmall
  have htailA8 : poissonTailError Λ a ≤ 1 / 8 := le_trans htailA (min_le_right _ _)
  have htailB8 : poissonTailError Λ b ≤ 1 / 8 := le_trans htailB (min_le_right _ _)
  have hfacA : (7 / 8 : ℝ) ^ 2 ≤ (1 - η) * (1 - poissonTailError Λ a) := by
    have hηfac : (7 / 8 : ℝ) ≤ 1 - η := by linarith
    have htailfac : (7 / 8 : ℝ) ≤ 1 - poissonTailError Λ a := by linarith
    calc
      (7 / 8 : ℝ) ^ 2 = (7 / 8) * (7 / 8) := by ring
      _ ≤ (7 / 8) * (1 - poissonTailError Λ a) :=
        mul_le_mul_of_nonneg_left htailfac (show (0 : ℝ) ≤ 7 / 8 by norm_num)
      _ ≤ (1 - η) * (1 - poissonTailError Λ a) :=
        mul_le_mul_of_nonneg_right hηfac (by linarith)
  have hfacB : (7 / 8 : ℝ) ^ 2 ≤ (1 - η) * (1 - poissonTailError Λ b) := by
    have hηfac : (7 / 8 : ℝ) ≤ 1 - η := by linarith
    have htailfac : (7 / 8 : ℝ) ≤ 1 - poissonTailError Λ b := by linarith
    calc
      (7 / 8 : ℝ) ^ 2 = (7 / 8) * (7 / 8) := by ring
      _ ≤ (7 / 8) * (1 - poissonTailError Λ b) :=
        mul_le_mul_of_nonneg_left htailfac (show (0 : ℝ) ≤ 7 / 8 by norm_num)
      _ ≤ (1 - η) * (1 - poissonTailError Λ b) :=
        mul_le_mul_of_nonneg_right hηfac (by linarith)
  have hlowA : Real.exp (-Λ) * (7 / 8 : ℝ) ^ 2 ≤ rho q a c := by
    calc
      Real.exp (-Λ) * (7 / 8 : ℝ) ^ 2 ≤
          Real.exp (-Λ) * ((1 - η) * (1 - poissonTailError Λ a)) :=
        mul_le_mul_of_nonneg_left hfacA (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-Λ) * (1 - η) * (1 - poissonTailError Λ a) := by ring
      _ ≤ rho q a c := hρA
  have hlowB : Real.exp (-Λ) * (7 / 8 : ℝ) ^ 2 ≤ rho q b c := by
    calc
      Real.exp (-Λ) * (7 / 8 : ℝ) ^ 2 ≤
          Real.exp (-Λ) * ((1 - η) * (1 - poissonTailError Λ b)) :=
        mul_le_mul_of_nonneg_left hfacB (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-Λ) * (1 - η) * (1 - poissonTailError Λ b) := by ring
      _ ≤ rho q b c := hρB

  rcases hI13b with ⟨hI13Product, _, _⟩
  rcases hI16c q a b (by omega) (by omega) (by omega) with ⟨_, hI16Drift⟩
  have hmono : MonotoneOn (finiteChi q a b c) (Set.Icc 0 c) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 c)
    · intro θ hθ
      exact (hI16b q a b (by omega) (by omega) (by omega) c hcPos θ hθ).continuousAt.continuousWithinAt
    · intro θ hθ
      exact (hI16b q a b (by omega) (by omega) (by omega) c hcPos θ
        (interior_subset hθ)).differentiableAt.differentiableWithinAt
    · intro θ hθ
      have hder := hI16b q a b (by omega) (by omega) (by omega) c hcPos θ
        (interior_subset hθ)
      rw [hder.deriv]
      exact hI16Drift c hcPos.le θ (interior_subset hθ)
  have hinterp : rho q a c * rho q b c ≤ rho q N c := by
    have hend := hI13Product q a b (by omega) (by omega) (by omega) c hcPos.le
    rw [← hend.1, ← hend.2]
    exact hmono (show (0 : ℝ) ∈ Set.Icc 0 c from ⟨le_rfl, hcPos.le⟩)
      (show c ∈ Set.Icc 0 c from ⟨hcPos.le, le_rfl⟩) hcPos.le
  have hρBnonneg : 0 ≤ rho q b c := le_trans (by positivity) hlowB
  have hlowProduct :
      (Real.exp (-Λ) * (7 / 8 : ℝ) ^ 2) *
        (Real.exp (-Λ) * (7 / 8 : ℝ) ^ 2) ≤ rho q a c * rho q b c := by
    calc
      _ ≤ (Real.exp (-Λ) * (7 / 8 : ℝ) ^ 2) * rho q b c :=
        mul_le_mul_of_nonneg_left hlowB (by positivity)
      _ ≤ rho q a c * rho q b c := mul_le_mul_of_nonneg_right hlowA hρBnonneg
  have hexpProduct :
      (Real.exp (-Λ) * (7 / 8 : ℝ) ^ 2) *
        (Real.exp (-Λ) * (7 / 8 : ℝ) ^ 2) =
          Real.exp (-2 * Λ) * (7 / 8 : ℝ) ^ 4 := by
    calc
      _ = (Real.exp (-Λ) * Real.exp (-Λ)) *
          ((7 / 8 : ℝ) ^ 2 * (7 / 8 : ℝ) ^ 2) := by ring
      _ = Real.exp (-Λ + -Λ) * ((7 / 8 : ℝ) ^ 2 * (7 / 8 : ℝ) ^ 2) := by
        rw [← Real.exp_add]
      _ = Real.exp (-2 * Λ) * (7 / 8 : ℝ) ^ 4 := by congr 1 <;> ring_nf
  have hnum : (1 / 2 : ℝ) < (7 / 8 : ℝ) ^ 4 := by norm_num
  have hthreshold : Real.exp (-2 * Λ) / 2 < Real.exp (-2 * Λ) * (7 / 8 : ℝ) ^ 4 := by
    have hm := mul_lt_mul_of_pos_left hnum (Real.exp_pos (-2 * Λ))
    nlinarith
  have hρlarge : Real.exp (-2 * Λ) / 2 < rho q N c := by
    calc
      Real.exp (-2 * Λ) / 2 < Real.exp (-2 * Λ) * (7 / 8 : ℝ) ^ 4 := hthreshold
      _ = (Real.exp (-Λ) * (7 / 8 : ℝ) ^ 2) *
          (Real.exp (-Λ) * (7 / 8 : ℝ) ^ 2) := hexpProduct.symm
      _ ≤ rho q a c * rho q b c := hlowProduct
      _ ≤ rho q N c := hinterp

  have hQ25Result := hQ25 q N hq hNq Λ η K c δ n₁ hΛ hδ hη hη₀ hw hN₁
    hcPos hcLeΛ hupperN htailηN hρlarge
  have hxiStrict :
      c - Λ / (N : ℝ) - K * δ N - (poissonDeviation N : ℝ) / N < xi q Λ η N :=
    hQ25Result.2

  rcases hQ23a with ⟨_, _, hEnvPlusAnti, _, _, hInvEnv⟩
  rcases hQ23b with ⟨hDev, _⟩
  let E : ℝ := envelope (u : ℝ)
  let R : ℝ := 1 / (u : ℝ)
  have huI : (u : ℝ) ∈ Set.Ici (Real.exp 2) := Set.mem_Ici.mpr huExp
  have haI : (a : ℝ) ∈ Set.Ici (Real.exp 2) := Set.mem_Ici.mpr haExp
  have hbI : (b : ℝ) ∈ Set.Ici (Real.exp 2) := Set.mem_Ici.mpr hbExp
  have hNI : (N : ℝ) ∈ Set.Ici (Real.exp 2) := Set.mem_Ici.mpr hNExp
  have hUa : (u : ℝ) ≤ a := by exact_mod_cast hua
  have hUb : (u : ℝ) ≤ b := by exact_mod_cast hub
  have hUN : (u : ℝ) ≤ N := by exact_mod_cast huN
  have hEnvA : envelope (a : ℝ) + 1 / (a : ℝ) ≤ E + R := by
    exact hEnvPlusAnti huI haI hUa
  have hEnvB : envelope (b : ℝ) + 1 / (b : ℝ) ≤ E + R := by
    exact hEnvPlusAnti huI hbI hUb
  have hEnvN : envelope (N : ℝ) + 1 / (N : ℝ) ≤ E + R := by
    exact hEnvPlusAnti huI hNI hUN
  have hDevA : (poissonDeviation a : ℝ) / a ≤ E + R :=
    le_trans (hDev a haPos).2 hEnvA
  have hDevB : (poissonDeviation b : ℝ) / b ≤ E + R :=
    le_trans (hDev b hbPos).2 hEnvB
  have hDevN : (poissonDeviation N : ℝ) / N ≤ E + R :=
    le_trans (hDev N hNPos).2 hEnvN
  have hDevA2 : 2 * (poissonDeviation a : ℝ) / a ≤ 2 * (E + R) := by
    calc
      2 * (poissonDeviation a : ℝ) / a =
          2 * ((poissonDeviation a : ℝ) / a) := by ring
      _ ≤ 2 * (E + R) := mul_le_mul_of_nonneg_left hDevA (by norm_num)
  have hDevB2 : 2 * (poissonDeviation b : ℝ) / b ≤ 2 * (E + R) := by
    calc
      2 * (poissonDeviation b : ℝ) / b =
          2 * ((poissonDeviation b : ℝ) / b) := by ring
      _ ≤ 2 * (E + R) := mul_le_mul_of_nonneg_left hDevB (by norm_num)
  have hShiftA : xi q Λ η a - 2 * (E + R) ≤
      xi q Λ η a - 2 * (poissonDeviation a : ℝ) / a := by
    linarith [hDevA2]
  have hShiftB : xi q Λ η b - 2 * (E + R) ≤
      xi q Λ η b - 2 * (poissonDeviation b : ℝ) / b := by
    linarith [hDevB2]
  have hMinShift :
      min (xi q Λ η a - 2 * (E + R)) (xi q Λ η b - 2 * (E + R)) =
        min (xi q Λ η a) (xi q Λ η b) - 2 * (E + R) := by
    by_cases h : xi q Λ η a ≤ xi q Λ η b
    · simp [min_eq_left h, min_eq_left (sub_le_sub_right h _)]
    · have h' : xi q Λ η b ≤ xi q Λ η a := le_of_not_ge h
      simp [min_eq_right h', min_eq_right (sub_le_sub_right h' _)]
  have hcLower : min (xi q Λ η a) (xi q Λ η b) - 2 * (E + R) ≤ c := by
    calc
      min (xi q Λ η a) (xi q Λ η b) - 2 * (E + R) =
          min (xi q Λ η a - 2 * (E + R)) (xi q Λ η b - 2 * (E + R)) := hMinShift.symm
      _ ≤ min (xi q Λ η a - 2 * (poissonDeviation a : ℝ) / a)
            (xi q Λ η b - 2 * (poissonDeviation b : ℝ) / b) := min_le_min hShiftA hShiftB
      _ = c := rfl

  have hInv : R ≤ E := by
    apply hInvEnv
    exact le_trans (Real.exp_le_exp.mpr (by norm_num)) huExp
  have hLambdaDiv : Λ / (N : ℝ) ≤ Λ * R := by
    calc
      Λ / (N : ℝ) ≤ Λ / (u : ℝ) :=
        div_le_div_of_nonneg_left hΛpos.le (by exact_mod_cast huPos) hUN
      _ = Λ * R := by simp [R, div_eq_mul_inv]
  have hdeltaN : δ N ≤ δ u := (hδ.2.1) u N huPos huN
  have hKdelta : K * δ N ≤ K * δ u :=
    mul_le_mul_of_nonneg_left hdeltaN hKpos.le
  have hcost : (Λ + 3) * R ≤ (Λ + 3) * E :=
    mul_le_mul_of_nonneg_left hInv (by linarith [hΛpos])
  have hbaseFinal :
      min (xi q Λ η a) (xi q Λ η b) -
        (K * δ u + (Λ + 6) * E) ≤
      c - Λ / (N : ℝ) - K * δ N - (poissonDeviation N : ℝ) / N := by
    calc
      min (xi q Λ η a) (xi q Λ η b) - (K * δ u + (Λ + 6) * E) ≤
          min (xi q Λ η a) (xi q Λ η b) - K * δ u - 3 * E - (Λ + 3) * R := by
        linarith only [hcost]
      _ = min (xi q Λ η a) (xi q Λ η b) - 2 * (E + R) - Λ * R -
          K * δ u - (E + R) := by ring
      _ ≤ c - Λ * R - K * δ u - (E + R) := by linarith only [hcLower]
      _ ≤ c - Λ / (N : ℝ) - K * δ N - (poissonDeviation N : ℝ) / N := by
        linarith only [hLambdaDiv, hKdelta, hDevN]

  have htarget :
      min (xi q Λ η a) (xi q Λ η b) - comparisonError δ Λ K (u : ℝ) ≤
        xi q Λ η N := by
    have hstrict := lt_of_le_of_lt hbaseFinal hxiStrict
    have hCE : comparisonError δ Λ K (u : ℝ) = K * δ u + (Λ + 6) * E := by
      simp [comparisonError, stepExtension, E, envelope, Nat.floor_natCast]
      ring
    rw [hCE]
    exact le_of_lt hstrict
  simpa [N, u] using htarget

end ThLean.W.SA48
