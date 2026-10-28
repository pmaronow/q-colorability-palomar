import ThLean.BP.S6.Potential

noncomputable section
open ThresholdFoundations
namespace ThLean.W.S627

theorem S6_26Statement_of_deps
    (h05 : ThLean.BP.S6.S6_05Statement)
    (h17 : ThLean.BP.S6.S6_17Statement)
    (h18 : ThLean.BP.S6.S6_18Statement) :
    ThLean.BP.S6.S6_26Statement := by
  intro n q hn hq G u e
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hsub : subgraph G (addPair G e) := by
    intro f
    by_cases hf : f = e.val
    · subst f
      simp [addPair, addEdge]
    · simp [addPair, addEdge, hf]
  by_cases hG : Colorable q G
  · have hsize := (h05 n q hn hq G u).2.2.2.2.2.2.2.1 hG
    have hcredit := (h17 n q hn hq G u).2.1 e
    let c : ℝ := (frozenClass q G u).card
    let a : ℝ := (credited q G u e).card
    have hcpos : 0 < c := by
      dsimp [c]
      exact_mod_cast hsize.1
    have hcone : 1 ≤ c := by
      dsimp [c]
      exact_mod_cast hsize.1
    have hannonneg : 0 ≤ a := by
      dsimp [a]
      positivity
    have hbudgetN : (frozenClass q G u).card + (credited q G u e).card ≤ n := hcredit.2
    have hbudget : c + a ≤ (n : ℝ) := by
      dsimp [c, a]
      exact_mod_cast hbudgetN
    have hargN : 1 + a / c ≤ (n : ℝ) / c := by
      calc
        1 + a / c = (c + a) / c := by
          have hcdiv : c / c = 1 := div_self (ne_of_gt hcpos)
          calc
            1 + a / c = c / c + a / c := by rw [← hcdiv]
            _ = (c + a) / c := by rw [add_div]
        _ ≤ (n : ℝ) / c := div_le_div_of_nonneg_right hbudget (le_of_lt hcpos)
    have hlogIncN : Real.log (1 + a / c) ≤ Real.log (n : ℝ) := by
      calc
        Real.log (1 + a / c) ≤ Real.log ((n : ℝ) / c) :=
          Real.log_le_log (by positivity) hargN
        _ = Real.log (n : ℝ) - Real.log c := by
          rw [Real.log_div (ne_of_gt hnR) (ne_of_gt hcpos)]
        _ ≤ Real.log (n : ℝ) := by
          have hcLog : 0 ≤ Real.log c := Real.log_nonneg hcone
          linarith
    have hlogIncNonneg : 0 ≤ Real.log (1 + a / c) :=
      Real.log_nonneg (by
        have hdiv : 0 ≤ a / c := div_nonneg hannonneg hcpos.le
        linarith)
    have hcurNonneg : 0 ≤ Real.log c := Real.log_nonneg hcone
    have hcurLeN : Real.log c ≤ Real.log (n : ℝ) := by
      apply Real.log_le_log (by positivity)
      change ((frozenClass q G u).card : ℝ) ≤ (n : ℝ)
      exact_mod_cast hsize.2
    have hinc : creditIncrement q G u e = Real.log (1 + a / c) := by
      simp [ThresholdFoundations.creditIncrement, hG, c, a]
    have hcur : ThLean.BP.S6.saturatedPotential q G u = Real.log c := by
      simp [ThLean.BP.S6.saturatedPotential, ThresholdFoundations.saturatedPotential,
        ThresholdFoundations.potential, hG, c]
    by_cases hAdd : Colorable q (addPair G e)
    · have habs := h18 n q hn hq G u e hG hAdd
      have hgrowN := habs.2.2.2
      have hnewpos : 0 < ((frozenClass q (addPair G e) u).card : ℝ) := by
        have hnewNat : 0 < (frozenClass q (addPair G e) u).card := by omega
        exact_mod_cast hnewNat
      have hgrow : c + a ≤ (frozenClass q (addPair G e) u).card := by
        dsimp [c, a]
        exact_mod_cast hgrowN
      have hargAdd : 1 + a / c ≤ (frozenClass q (addPair G e) u).card / c := by
        calc
          1 + a / c = (c + a) / c := by
            have hcdiv : c / c = 1 := div_self (ne_of_gt hcpos)
            calc
              1 + a / c = c / c + a / c := by rw [← hcdiv]
              _ = (c + a) / c := by rw [add_div]
          _ ≤ (frozenClass q (addPair G e) u).card / c :=
            div_le_div_of_nonneg_right hgrow (le_of_lt hcpos)
      have hlogGrow : Real.log (1 + a / c) ≤
          Real.log ((frozenClass q (addPair G e) u).card : ℝ) - Real.log c := by
        calc
          Real.log (1 + a / c) ≤
              Real.log ((frozenClass q (addPair G e) u).card / c) :=
            Real.log_le_log (by positivity) hargAdd
          _ = Real.log ((frozenClass q (addPair G e) u).card : ℝ) - Real.log c := by
            rw [Real.log_div (ne_of_gt hnewpos) (ne_of_gt hcpos)]
      have hnew : ThLean.BP.S6.saturatedPotential q (addPair G e) u =
          Real.log ((frozenClass q (addPair G e) u).card : ℝ) := by
        simp [ThLean.BP.S6.saturatedPotential, ThresholdFoundations.saturatedPotential,
          ThresholdFoundations.potential, hAdd]
      rw [hinc, hcur, hnew]
      exact ⟨hcurNonneg, hcurLeN, hlogIncNonneg, hlogGrow, hlogIncN⟩
    · have hnew : ThLean.BP.S6.saturatedPotential q (addPair G e) u =
          Real.log (n : ℝ) := by
        simp [ThLean.BP.S6.saturatedPotential, ThresholdFoundations.saturatedPotential, hAdd]
      have hlogFail : Real.log (1 + a / c) ≤ Real.log (n : ℝ) - Real.log c := by
        calc
          Real.log (1 + a / c) ≤ Real.log ((n : ℝ) / c) :=
            Real.log_le_log (by positivity) hargN
          _ = Real.log (n : ℝ) - Real.log c := by
            rw [Real.log_div (ne_of_gt hnR) (ne_of_gt hcpos)]
      have hlogIncN' : Real.log (1 + a / c) ≤ Real.log (n : ℝ) := by
        have hcLog : 0 ≤ Real.log c := Real.log_nonneg hcone
        linarith
      rw [hinc, hcur, hnew]
      exact ⟨hcurNonneg, hcurLeN, hlogIncNonneg, hlogFail, hlogIncN'⟩
  · have hAdd : ¬ Colorable q (addPair G e) := by
      intro hAdd
      apply hG
      obtain ⟨σ, hσ⟩ := hAdd
      exact ⟨σ, fun a b hab => hσ a b (lt_of_lt_of_le hab (hsub (s(a, b))))⟩
    simp [ThLean.BP.S6.saturatedPotential, ThresholdFoundations.saturatedPotential,
      ThresholdFoundations.creditIncrement, hG, hAdd, hlogn]

end ThLean.W.S627
