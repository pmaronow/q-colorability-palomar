import ThLean.W.S370S.CodeLists
import ThLean.W.S370S.Realize
import ThLean.W.S370S.Sizing

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S370S
open ThresholdFoundations ThLean.BP.S3
variable {V : Type u} [Fintype V]

theorem dumbbellCode_shared {k : ℕ} (hk : 0 < k) (j₁ j₂ : ℕ)
    (labels : Fin k ↪ V) (h₁ : 2 ≤ j₁) (h₂ : 2 ≤ j₂) (hs : j₁+j₂=k+1) :
    ExactDumbbell (dumbbellCode hk j₁ j₂ 0 labels) ∧
      (vertexSupport (dumbbellCode hk j₁ j₂ 0 labels)).card = k := by
  let v₁ : Fin j₁ → V := fun i => labels ⟨i.val, by omega⟩
  let v₂ : Fin j₂ → V := fun i => labels
    ⟨if i.val = 0 then 0 else j₁+i.val-1, by split_ifs <;> omega⟩
  let w : Fin (0+1) → V := fun _ => labels ⟨0,hk⟩
  have hv₁ : Function.Injective v₁ := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin k => x.val) (labels.injective h))
  have hv₂ : Function.Injective v₂ := by
    intro i j h
    have hh := congrArg Fin.val (labels.injective h)
    dsimp [v₂] at hh
    apply Fin.ext
    split_ifs at hh <;> omega
  have hinter : Finset.univ.image v₁ ∩ Finset.univ.image v₂ = {labels ⟨0,hk⟩} := by
    ext a
    constructor
    · rintro ha
      obtain ⟨ha₁, ha₂⟩ := Finset.mem_inter.mp ha
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha₁
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp ha₂
      have hh := congrArg Fin.val (labels.injective (hi.trans hj.symm))
      dsimp [v₁, v₂] at hh
      have hi0 : i.val = 0 := by split_ifs at hh <;> omega
      apply Finset.mem_singleton.mpr
      rw [← hi]
      exact congrArg labels (Fin.ext hi0)
    · intro ha
      have ha' := Finset.mem_singleton.mp ha
      subst a
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_image.mpr ⟨⟨0,by omega⟩, Finset.mem_univ _, rfl⟩,
         Finset.mem_image.mpr ⟨⟨0,by omega⟩, Finset.mem_univ _, by simp [v₂]⟩⟩
  have hb : codeLabel hk labels 0 = labels ⟨0,hk⟩ := codeLabel_eq hk labels hk
  have hfirst : (List.range j₁).map (codeLabel hk labels) = List.ofFn v₁ := by
    simpa only [Nat.zero_add] using codeLabel_window hk labels 0 (n := j₁) (by omega)
  have hsecond : [codeLabel hk labels 0] ++
      (List.range (j₂-1)).map (fun i => codeLabel hk labels (j₁+i)) = List.ofFn v₂ := by
    apply cons_range_eq_ofFn (by omega)
    · simp [v₂, hb]
    · intro i
      rw [codeLabel_eq hk labels (by omega)]
      dsimp only [v₂]
      apply congrArg labels
      apply Fin.ext
      simp [show i.val+1 ≠ 0 by omega, Nat.add_assoc]
  have heq : dumbbellCode hk j₁ j₂ 0 labels =
      edgesGraph (cyclePairs (by omega) v₁ ++ cyclePairs (by omega) v₂ ++ pathPairs w) := by
    unfold dumbbellCode
    simp only [ite_true, ← List.append_assoc]
    rw [hfirst, hsecond, hb]
    change edgesGraph (consecutiveEdges (List.ofFn v₁ ++ [v₁ ⟨0,by omega⟩]) ++
      consecutiveEdges (List.ofFn v₂ ++ [v₂ ⟨0,by omega⟩])) = _
    rw [consecutiveEdges_cycle, consecutiveEdges_cycle]
    simp [cyclePairs, pathPairs]
  have hex : ExactDumbbell (dumbbellCode hk j₁ j₂ 0 labels) := by
    rw [heq]
    apply realize_dumbbell h₁ h₂ v₁ v₂ w hv₁ hv₂
    · intro i j _
      apply Fin.ext
      have := i.isLt
      have := j.isLt
      omega
    · exact Or.inl ⟨rfl, by rw [hinter]; simp⟩
  refine ⟨hex, ?_⟩
  have hsize := (exactDumbbell_size hex).2
  have hcount := dumbbellCode_edgeCount hk j₁ j₂ 0 labels h₁ h₂ (by omega)
  omega

end ThLean.W.S370S
