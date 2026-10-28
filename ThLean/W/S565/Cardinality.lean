import ThLean.BP.S5.Structure

noncomputable section

namespace ThLean.W.S565

open ThresholdFoundations

theorem S5_04AStatement_holds : ThLean.BP.S5.S5_04AStatement := by
  intro V inst Z
  classical
  change Fintype.card (Option {v : V // v ∉ Z}) =
    Fintype.card V - Z.card + 1
  simp only [Fintype.card_option, Fintype.card_subtype_compl]
  rw [Fintype.card_subtype]
  simp

example : ThLean.BP.S5.S5_04AStatement := S5_04AStatement_holds

end ThLean.W.S565
