import ThLean.W.S370S.CodeLists
import ThLean.W.S370S.Realize
import ThLean.W.S370S.Sizing

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S370S
open ThresholdFoundations ThLean.BP.S3
variable {V : Type u} [Fintype V]

private theorem image_inter_singleton {n m : ℕ} (f : Fin n → V) (g : Fin m → V)
    (a : V) (hf : a ∈ Finset.univ.image f) (hg : a ∈ Finset.univ.image g)
    (h : ∀ i j, f i = g j → f i = a) :
    Finset.univ.image f ∩ Finset.univ.image g = {a} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hy⟩ := Finset.mem_inter.mp hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy
    exact Finset.mem_singleton.mpr (hi.symm.trans (h i j (hi.trans hj.symm)))
  · intro hx
    have := Finset.mem_singleton.mp hx
    subst x
    exact Finset.mem_inter.mpr ⟨hf,hg⟩

theorem dumbbellCode_joined {k : ℕ} (hk : 0 < k) (j₁ j₂ j₃ : ℕ)
    (labels : Fin k ↪ V) (h₁ : 2 ≤ j₁) (h₂ : 2 ≤ j₂) (h₃ : 0 < j₃)
    (hs : j₁+j₂+j₃=k+1) :
    ExactDumbbell (dumbbellCode hk j₁ j₂ j₃ labels) ∧
      (vertexSupport (dumbbellCode hk j₁ j₂ j₃ labels)).card = k := by
  let v₁ : Fin j₁ → V := fun i => labels ⟨i.val, by omega⟩
  let v₂ : Fin j₂ → V := fun i => labels ⟨j₁+i.val, by omega⟩
  let w : Fin (j₃+1) → V := fun i => labels
    ⟨if i.val=0 then 0 else if i.val=j₃ then j₁ else j₁+j₂+i.val-1,
      by split_ifs <;> omega⟩
  have hv₁ : Function.Injective v₁ := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin k => x.val) (labels.injective h))
  have hv₂ : Function.Injective v₂ := by
    intro i j h
    have hh := congrArg (fun x : Fin k => x.val) (labels.injective h)
    dsimp [v₂] at hh
    apply Fin.ext
    omega
  have hw : Function.Injective w := by
    intro i j h
    have hh := congrArg (fun x : Fin k => x.val) (labels.injective h)
    dsimp [w] at hh
    apply Fin.ext
    split_ifs at hh <;> omega
  have hw0 : w 0 = labels ⟨0,hk⟩ := by simp [w]
  have hwn : w (Fin.last j₃) = labels ⟨j₁,by omega⟩ := by
    simp [w, Fin.last, show j₃ ≠ 0 by omega]
  have hv : Disjoint (Finset.univ.image v₁) (Finset.univ.image v₂) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb
    have hh := congrArg (fun x : Fin k => x.val) (labels.injective (hi.trans hj.symm))
    dsimp [v₁,v₂] at hh
    omega
  have ha : w 0 ∈ Finset.univ.image v₁ :=
    Finset.mem_image.mpr ⟨⟨0,by omega⟩, Finset.mem_univ _, hw0.symm⟩
  have hb : w (Fin.last j₃) ∈ Finset.univ.image v₂ :=
    Finset.mem_image.mpr ⟨⟨0,by omega⟩, Finset.mem_univ _, by simpa [v₂] using hwn.symm⟩
  have hpa : Finset.univ.image w ∩ Finset.univ.image v₁ = {w 0} := by
    apply image_inter_singleton w v₁ (w 0) (by simp) ha
    intro i j hij
    have hh := congrArg (fun x : Fin k => x.val) (labels.injective hij)
    dsimp [w,v₁] at hh
    have hi : i.val=0 := by split_ifs at hh <;> omega
    exact congrArg w (Fin.ext hi)
  have hpb : Finset.univ.image w ∩ Finset.univ.image v₂ = {w (Fin.last j₃)} := by
    apply image_inter_singleton w v₂ (w (Fin.last j₃)) (by simp) hb
    intro i j hij
    have hh := congrArg (fun x : Fin k => x.val) (labels.injective hij)
    dsimp [w,v₂] at hh
    have hi : i.val=j₃ := by split_ifs at hh <;> omega
    exact congrArg w (Fin.ext hi)
  have hbase : codeLabel hk labels 0 = labels ⟨0,hk⟩ := codeLabel_eq hk labels hk
  have hatt : codeLabel hk labels j₁ = labels ⟨j₁,by omega⟩ :=
    codeLabel_eq hk labels (by omega)
  have hfirst : (List.range j₁).map (codeLabel hk labels) = List.ofFn v₁ := by
    simpa only [Nat.zero_add] using codeLabel_window hk labels 0 (n := j₁) (by omega)
  have hsecond : (List.range j₂).map (fun i => codeLabel hk labels (j₁+i)) =
      List.ofFn v₂ := codeLabel_window hk labels j₁ (by omega)
  have hpath : ([codeLabel hk labels 0] ++
      (List.range (j₃-1)).map (fun i => codeLabel hk labels (j₁+j₂+i))) ++
      [codeLabel hk labels j₁] = List.ofFn w := by
    apply cons_range_append_eq_ofFn h₃
    · exact hw0.trans hbase.symm
    · exact hwn.trans hatt.symm
    · intro i
      rw [codeLabel_eq hk labels (by omega)]
      dsimp only [w]
      apply congrArg labels
      apply Fin.ext
      simp [show i.val+1 ≠ 0 by omega, show i.val+1 ≠ j₃ by omega, ← Nat.add_assoc]
  have heq : dumbbellCode hk j₁ j₂ j₃ labels =
      edgesGraph (cyclePairs (by omega) v₁ ++ cyclePairs (by omega) v₂ ++ pathPairs w) := by
    unfold dumbbellCode
    rw [if_neg (by omega)]
    try simp only [← List.append_assoc]
    rw [hfirst,hsecond,hpath,hbase,hatt]
    change edgesGraph (consecutiveEdges (List.ofFn v₁ ++ [v₁ ⟨0,by omega⟩]) ++
      consecutiveEdges (List.ofFn v₂ ++ [v₂ ⟨0,by omega⟩]) ++
      consecutiveEdges (List.ofFn w)) = _
    rw [consecutiveEdges_cycle,consecutiveEdges_cycle,consecutiveEdges_ofFn]
    simp [cyclePairs,pathPairs,List.append_assoc]
  have hex : ExactDumbbell (dumbbellCode hk j₁ j₂ j₃ labels) := by
    rw [heq]
    exact realize_dumbbell h₁ h₂ v₁ v₂ w hv₁ hv₂ hw
      (Or.inr ⟨by omega, hv, ha, hb, hpa, hpb⟩)
  refine ⟨hex, ?_⟩
  have hsize := (exactDumbbell_size hex).2
  have hcount := dumbbellCode_edgeCount hk j₁ j₂ j₃ labels h₁ h₂ hs
  omega

end ThLean.W.S370S
