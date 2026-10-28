import ThLean.BP.S5.Structure

noncomputable section

attribute [local instance] Classical.propDecidable

namespace ThLean.W.S566

open ThresholdFoundations

private theorem mapGraph_pos_of_pos {V W : Type*} [Fintype V] [Fintype W]
    (f : V → W) (G : MGraph V) (e : Sym2 V) (he : 0 < G e) :
    0 < mapGraph f G (Sym2.map f e) := by
  unfold mapGraph
  apply lt_of_lt_of_le he
  simpa using
    (Finset.single_le_sum
      (f := fun x : Sym2 V => if Sym2.map f x = Sym2.map f e then G x else 0)
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ e))

theorem S5_04BStatement_holds : ThLean.BP.S5.S5_04BStatement := by
  intro V inst q B Z u hu v hv hedge
  have hmapped :
      Sym2.map (identifyVertex Z) (s(u, v)) = s(none, none) := by
    simp [identifyVertex, hu, hv]
  have hloop : 0 < identify B Z (s(none, none)) := by
    rw [identify]
    rw [← hmapped]
    exact mapGraph_pos_of_pos (identifyVertex Z) B (s(u, v)) hedge
  rintro ⟨τ, hcolor⟩
  exact hcolor none none hloop rfl

example : ThLean.BP.S5.S5_04BStatement := S5_04BStatement_holds

end ThLean.W.S566
