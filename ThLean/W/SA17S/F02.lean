import ThLean.BP.SA.Basics
import ThLean.W.S309.Process
import ThLean.W.S310.S3_04a
import ThLean.W.S312.Process
import ThLean.W.S314.Quantile

noncomputable section

namespace ThLean.W.SA17S

open ThresholdFoundations

/-- The strict upper tail continues past the cap by decreasing survival. -/
theorem SA_F02Statement_holds : ThLean.BP.SA.SA_F02Statement := by
  intro q hq Λ η _hΛ hη hηhalf n hn hUcap m hUm
  have hq2 : 2 ≤ q := by omega
  have hn2 : 2 ≤ Fintype.card (Fin n) := by simp only [Fintype.card_fin]; omega
  have hprocess : ThLean.BP.S3.S3_04aStatement.{0} :=
    ThLean.W.S310.S3_04aStatement_of_deps ThLean.W.S309.S3_02Statement_holds
  have hcaplaw := ThLean.W.S312.S3_05Statement_of_deps
    hprocess ThLean.W.S309.S3_02Statement_holds
  have hquant := ThLean.W.S314.S3_06bStatement_holds
    (Fin n) q (cap Λ n) η hn2 hη hηhalf
  have hnext : upperLocation q Λ η n + 1 ≤ cap Λ n := by omega
  have htail : cappedTail (V := Fin n) q (cap Λ n)
      (upperLocation q Λ η n + 1) < η :=
    hquant.2.2.2.2.2.1 _ (Nat.lt_succ_self _) hnext
  have hidentity := (hcaplaw (Fin n) q (cap Λ n) hq2 hn2).2.2.1
    (upperLocation q Λ η n + 1) hnext
  rw [hidentity] at htail
  have hmono : Antitone (processSurvival (V := Fin n) q) :=
    (hprocess (Fin n) q hq2).2.2.2
  exact lt_of_le_of_lt (hmono (by omega : upperLocation q Λ η n + 1 ≤ m)) htail

example : ThLean.BP.SA.SA_F02Statement := SA_F02Statement_holds

end ThLean.W.SA17S
