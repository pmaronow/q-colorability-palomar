module

public import ThLean.BP.SA.Tree

@[expose] public section

noncomputable section
open Filter
open scoped Topology

namespace ThLean.W.SA63

theorem SA_T37Statement_holds : ThLean.BP.SA.SA_T37Statement := by
  intro ξ E s₀ s₁ B hs₀ hs₁ hB hξ hE hEt htail
  have hξUpper : ∀ᶠ n : ℕ in atTop, ξ n ≤ B := by
    filter_upwards [eventually_atTop.2 ⟨s₀, fun _ hn => hn⟩] with n hn
    exact (abs_le.mp (hξ n hn)).2
  have hξLower : ∀ᶠ n : ℕ in atTop, -B ≤ ξ n := by
    filter_upwards [eventually_atTop.2 ⟨s₀, fun _ hn => hn⟩] with n hn
    exact (abs_le.mp (hξ n hn)).1
  have hξBound : IsBoundedUnder (· ≤ ·) atTop ξ :=
    Filter.isBoundedUnder_of_eventually_le hξUpper
  have hξCobound : IsCoboundedUnder (· ≤ ·) atTop ξ :=
    Filter.isCoboundedUnder_le_of_eventually_le atTop hξLower
  apply tendsto_order.2
  constructor
  · intro b hb
    let c : ℝ := (b + Filter.limsup ξ atTop) / 2
    have hbc : b < c := by dsimp [c]; linarith
    have hcL : c < Filter.limsup ξ atTop := by dsimp [c]; linarith
    have hfreq : ∃ᶠ ℓ : ℕ in atTop, c < ξ ℓ :=
      frequently_lt_of_lt_limsup hξCobound hcL
    have hEsmall : ∀ᶠ ℓ : ℕ in atTop, E ℓ < c - b :=
      (tendsto_order.1 hEt).2 (c - b) (by linarith)
    have hs1event : ∀ᶠ ℓ : ℕ in atTop, s₁ ≤ ℓ :=
      eventually_atTop.2 ⟨s₁, fun _ hn => hn⟩
    obtain ⟨ℓ, hnear, ⟨herr, hℓ⟩⟩ :=
      (hfreq.and_eventually (hEsmall.and hs1event)).exists
    have hbase : b < ξ ℓ - E ℓ := by linarith
    filter_upwards [eventually_atTop.2 ⟨ℓ ^ 2, fun n hn => hn⟩] with n hn
    exact hbase.trans_le (htail ℓ hℓ n hn)
  · intro b hb
    exact eventually_lt_of_limsup_lt hb hξBound

end ThLean.W.SA63
