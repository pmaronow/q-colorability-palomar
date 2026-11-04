module

public import ThLean.BP.S3.Cycles

@[expose] public section

noncomputable section

namespace ThLean.W.S359

open ThresholdFoundations

theorem S3_56Statement_holds : ThLean.BP.S3.S3_56Statement := by
  classical
  intro V _ q hq B hB
  have h2q : 2 ≤ q := by omega
  obtain ⟨σ, hσ⟩ := hB
  let lift : V → Fin q := fun v => Fin.castLE h2q (σ v)
  have hlift : IsColoring q B lift := by
    intro u v huv
    exact fun heq => hσ u v huv (Fin.castLE_injective h2q heq)
  constructor
  · exact ⟨lift, hlift⟩
  · intro e
    rcases e with ⟨z, hz⟩
    induction z using Sym2.ind with
    | h a b =>
      have hab : a ≠ b := by
        intro hab
        subst b
        exact hz a rfl
      let third : Fin q := ⟨2, by omega⟩
      have hthird (v : V) : third ≠ lift v := by
        intro heq
        have hv := congrArg Fin.val heq
        simp [third, lift] at hv
        omega
      let τ : V → Fin q := Function.update lift a third
      refine ⟨τ, ?_⟩
      intro u v huv
      by_cases he : s(u, v) = s(a, b)
      · rcases (Sym2.eq).mp he with ⟨hua, hvb⟩ | ⟨hub, hva⟩
        ·
          change Function.update lift a third a ≠ Function.update lift a third b
          simp only [Function.update_self, Function.update_of_ne hab.symm]
          exact hthird b
        ·
          change Function.update lift a third b ≠ Function.update lift a third a
          simp only [Function.update_of_ne hab.symm, Function.update_self]
          exact (hthird b).symm
      · have hBuv : 0 < B (s(u, v)) := by
          change 0 < Function.update B (s(a, b)) (B (s(a, b)) + 1) (s(u, v)) at huv
          rw [Function.update_of_ne he] at huv
          exact huv
        have hbase := hlift u v hBuv
        change Function.update lift a third u ≠ Function.update lift a third v
        by_cases hua : u = a
        · subst u
          by_cases hva : v = a
          · subst v
            exact False.elim (hbase rfl)
          · simp only [Function.update_self, Function.update_of_ne hva]
            exact hthird v
        · by_cases hva : v = a
          · subst v
            simp only [Function.update_of_ne hua, Function.update_self]
            exact (hthird u).symm
          · simp only [Function.update_of_ne hua, Function.update_of_ne hva]
            exact hbase

example : ThLean.BP.S3.S3_56Statement := S3_56Statement_holds

end ThLean.W.S359
