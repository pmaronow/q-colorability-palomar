import ThLean.Contrib.SA17.FoundationInputs

noncomputable section
namespace ThLean.W.SA17

theorem SA_F02Statement_of_deps
    (hquant : ThresholdFoundations.PreQuantileStatement)
    (hproj : ThresholdFoundations.ProjectiveConsistencyStatement) :
    ThLean.BP.SA.SA_F02Statement := by
  intro q hq Λ η hΛ hη hηhalf n hn hUcap m hUm
  have hn2 : 2 ≤ n := by omega
  have hq1 : 1 ≤ q := by omega
  have hmono : Antitone (ThresholdFoundations.processSurvival (V := Fin n) q) :=
    (hproj.2 q n hq1 hn2).1
  have hquant' := hquant q n (ThresholdFoundations.cap Λ n) hq hn2 η hη hηhalf
  rcases hquant' with ⟨_, _, _, _, _, _, _, htail⟩
  have hU1le :
      ThresholdFoundations.upperLocation q Λ η n + 1 ≤
        ThresholdFoundations.cap Λ n := by
    dsimp [ThresholdFoundations.upperLocation, ThresholdFoundations.cap] at hUcap ⊢
    omega
  have hbase :
      ThresholdFoundations.processSurvival (V := Fin n) q
          (ThresholdFoundations.upperLocation q Λ η n + 1) < η := by
    apply htail (ThresholdFoundations.upperLocation q Λ η n + 1)
    · exact Nat.lt_succ_self _
    · exact hU1le
  have hstep : ThresholdFoundations.upperLocation q Λ η n + 1 ≤ m := by
    omega
  exact lt_of_le_of_lt (hmono hstep) hbase

theorem SA_F02Statement_of_foundationInputs
    (h : ThLean.Contrib.SA17.SA_F02FoundationInputsStatement) :
    ThLean.BP.SA.SA_F02Statement :=
  SA_F02Statement_of_deps h.1 h.2

end ThLean.W.SA17
