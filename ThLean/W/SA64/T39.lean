import ThLean.BP.SA.Tree
import ThLean.BP.SA.Quantiles

noncomputable section
open Filter
open scoped Topology

namespace ThLean.W.SA64
open ThresholdFoundations
open ThLean.BP.SA

/-- The comparison error has the tree hypotheses, assuming the two analytic
inputs isolated as sibling leaves Q23a and Q23c. -/
theorem SA_T39Statement_of_deps
    (h23a : SA_Q23aStatement) (h23c : SA_Q23cStatement) :
    SA_T39Statement := by
  intro Λ K δ hΛ hK hδ
  rcases hδ with ⟨hδpos, hδmono, hδsum⟩
  rcases h23a with ⟨_hEnvelopePos, hEnvelopeAnti, _hEnvelopePlusAnti,
    _hEnvelopeLimit, _hEnvelopePlusLimit, _hEnvelopeLower⟩
  have hform (u : ℝ) :
      comparisonError δ Λ K u =
        K * δ (Nat.floor u) + (Λ + 6) * envelope u := by
    unfold ThresholdFoundations.comparisonError ThresholdFoundations.stepExtension
      ThLean.BP.SA.envelope
    ring
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact Real.one_le_exp (by norm_num)
    · intro u hu
      rw [hform]
      have huFloor : 1 ≤ Nat.floor u := Nat.le_floor (by exact_mod_cast hu)
      have hδu : 0 < δ (Nat.floor u) := (hδpos _ huFloor).1
      have hEnvelope : 0 ≤ envelope u := by
        unfold envelope
        exact div_nonneg (Real.log_nonneg hu) (Real.sqrt_nonneg _)
      have hΛ6 : 0 < Λ + 6 := by linarith
      exact add_nonneg (mul_nonneg hK.le hδu.le)
        (mul_nonneg hΛ6.le hEnvelope)
    · intro u hu v hv huv
      rw [hform, hform]
      have hexp2 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
      have hu1 : (1 : ℝ) ≤ u := hexp2.trans hu
      have hflooru : 1 ≤ Nat.floor u := Nat.le_floor (by exact_mod_cast hu1)
      have hflooruv : Nat.floor u ≤ Nat.floor v := Nat.floor_mono huv
      have hδuv : δ (Nat.floor v) ≤ δ (Nat.floor u) :=
        hδmono _ _ hflooru hflooruv
      have henvuv : envelope v ≤ envelope u := hEnvelopeAnti hu hv huv
      have hΛ6 : 0 ≤ Λ + 6 := by linarith
      have hδscaled : K * δ (Nat.floor v) ≤ K * δ (Nat.floor u) :=
        mul_le_mul_of_nonneg_left hδuv hK.le
      have henvscaled : (Λ + 6) * envelope v ≤ (Λ + 6) * envelope u :=
        mul_le_mul_of_nonneg_left henvuv hΛ6
      linarith
    · have hEnvelopeSample : ∀ k : ℕ,
          envelope (Real.exp ((k : ℝ) + 1)) =
            ((k : ℝ) + 1) * Real.exp (-((k : ℝ) + 1) / 2) := by
        intro k
        unfold envelope
        rw [Real.log_exp]
        let x : ℝ := (k : ℝ) + 1
        have hratio : x / Real.sqrt (Real.exp x) = x * Real.exp (-x / 2) := by
          calc
            x / Real.sqrt (Real.exp x) = x * (Real.exp (x / 2))⁻¹ := by
              rw [← Real.exp_half x, div_eq_mul_inv]
            _ = x * Real.exp (-(x / 2)) := by rw [← Real.exp_neg]
            _ = x * Real.exp (-x / 2) := by congr 1; ring_nf
        simpa [x] using hratio
      have hsumBase : Summable (fun k : ℕ =>
          K * δ (Nat.floor (Real.exp ((k : ℝ) + 1))) +
            (Λ + 6) * (((k : ℝ) + 1) *
              Real.exp (-((k : ℝ) + 1) / 2))) :=
        (hδsum.mul_left K).add (h23c.mul_left (Λ + 6))
      have hsum : Summable (fun k : ℕ =>
          comparisonError δ Λ K (Real.exp ((k : ℝ) + 1))) := by
        apply hsumBase.congr
        intro k
        rw [hform, hEnvelopeSample]
      exact hsum
  · constructor
    · intro u hu
      rw [hform]
      have huFloor : 1 ≤ Nat.floor u := Nat.le_floor (by exact_mod_cast hu)
      have hδu : 0 < δ (Nat.floor u) := (hδpos _ huFloor).1
      have huPos : 0 < u := lt_of_lt_of_le zero_lt_one hu
      have hlog : 0 ≤ Real.log u := Real.log_nonneg hu
      have hsqrt : 0 < Real.sqrt u := Real.sqrt_pos.2 huPos
      have hEnvelope : 0 ≤ envelope u := by
        unfold envelope
        exact div_nonneg hlog hsqrt.le
      have hΛ6 : 0 < Λ + 6 := by linarith
      exact add_pos_of_pos_of_nonneg (mul_pos hK hδu)
        (mul_nonneg hΛ6.le hEnvelope)
    · have hsample : Tendsto
          (fun k : ℕ => δ (Nat.floor (Real.exp ((k : ℝ) + 1))))
          atTop (𝓝 0) := hδsum.tendsto_atTop_zero
      have hδlimit : Tendsto δ atTop (𝓝 0) := by
        refine tendsto_order.2 ⟨?_, ?_⟩
        · intro a ha
          apply eventually_atTop.2
          refine ⟨1, ?_⟩
          intro n hn
          exact lt_trans ha (hδpos n hn).1
        · intro b hb
          have hevent := (tendsto_order.1 hsample).2 b hb
          obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hevent
          let N : ℕ := Nat.floor (Real.exp ((k₀ : ℝ) + 1))
          have hN : 1 ≤ N := by
            dsimp [N]
            apply Nat.le_floor
            exact_mod_cast (Real.one_le_exp (by positivity))
          have hsampleSmall : δ N < b := by
            dsimp [N]
            exact hk₀ k₀ le_rfl
          apply eventually_atTop.2
          refine ⟨N, ?_⟩
          intro n hn
          calc
            δ n ≤ δ N := hδmono N n hN hn
            _ < b := hsampleSmall
      exact hδlimit

end ThLean.W.SA64
