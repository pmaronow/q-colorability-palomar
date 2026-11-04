module

public import ThLean.BP.S4.Deletion

@[expose] public section

noncomputable section
open scoped BigOperators
namespace ThLean.W.S415
open ThresholdFoundations ThLean.BP.S4

private def red03Tail {E : Type} {T : ℕ} (x : Fin T → E) (l : ℕ)
    (hl : l ≤ T) : Fin (T-l) → E :=
  fun j => x ⟨l + j.val, by have := j.isLt; omega⟩

private def red03Encode {E : Type} {T m l : ℕ} (i : Fin T)
    (hi : i.val < m) (hm : m ≤ l) (hl : l ≤ T)
    (p : (Fin (m-1) → E) × (E × ((Fin (l-m) → E) × (Fin (T-l) → E)))) : Fin T → E :=
  fun k =>
    if hk : k.val < i.val then
      p.1 ⟨k.val, by have := i.isLt; omega⟩
    else if he : k.val = i.val then
      p.2.1
    else if hm' : k.val < m then
      p.1 ⟨k.val - 1, by have := k.isLt; omega⟩
    else if hl' : k.val < l then
      p.2.2.1 ⟨k.val - m, by have := k.isLt; omega⟩
    else
      p.2.2.2 ⟨k.val - l, by have := k.isLt; omega⟩

private def red03Decode {E : Type} {T m l : ℕ} (x : Fin T → E) (i : Fin T)
    (hi : i.val < m) (hm : m ≤ l) (hl : l ≤ T) :
    (Fin (m-1) → E) × (E × ((Fin (l-m) → E) × (Fin (T-l) → E))) :=
  (omitBlock x i m hi (le_trans hm hl), x i,
    futureBlock x m l hm hl, red03Tail x l hl)

private theorem red03EncodeDecode {E : Type} {T m l : ℕ} (i : Fin T)
    (hi : i.val < m) (hm : m ≤ l) (hl : l ≤ T) (x : Fin T → E) :
    red03Encode i hi hm hl (red03Decode x i hi hm hl) = x := by
  funext k
  by_cases hki : k.val < i.val
  · simp [red03Encode, red03Decode, hki, omitBlock]
  · by_cases hke : k.val = i.val
    · have hk : k = i := Fin.ext hke
      subst k
      simp [red03Encode, red03Decode]
    · have hik : i.val < k.val := by omega
      by_cases hkm : k.val < m
      · have hsub : ¬ k.val - 1 < i.val := by omega
        simp only [red03Encode, red03Decode, hki, hke, hkm]
        unfold omitBlock
        simp [hsub]
        apply congrArg x
        apply Fin.ext
        simp
        omega
      · by_cases hkl : k.val < l
        · simp only [red03Encode, red03Decode, hki, hke, hkm, hkl]
          unfold futureBlock
          apply congrArg x
          apply Fin.ext
          simp
          omega
        · simp only [red03Encode, red03Decode, hki, hke, hkm, hkl]
          unfold red03Tail
          apply congrArg x
          apply Fin.ext
          simp
          omega

private theorem red03DecodeEncode {E : Type} {T m l : ℕ} (i : Fin T)
    (hi : i.val < m) (hm : m ≤ l) (hl : l ≤ T)
    (p : (Fin (m-1) → E) × (E × ((Fin (l-m) → E) × (Fin (T-l) → E)))) :
    red03Decode (red03Encode i hi hm hl p) i hi hm hl = p := by
  apply Prod.ext
  · funext j
    by_cases hj : j.val < i.val
    · have hk : j.val < i.val := hj
      simp [red03Decode, red03Encode, omitBlock, hk]
    · have hk0 : ¬ (j.val + 1 < i.val) := by omega
      have hk1 : j.val + 1 ≠ i.val := by omega
      have hkm : j.val + 1 < m := by have := j.isLt; omega
      simp [red03Decode, red03Encode, omitBlock, hj, hk0, hk1, hkm]
  · apply Prod.ext
    · simp [red03Decode, red03Encode]
    · apply Prod.ext
      · funext j
        have hk0 : ¬ (m + j.val < i.val) := by omega
        have hk1 : m + j.val ≠ i.val := by omega
        have hk2 : ¬ (m + j.val < m) := by omega
        have hk3 : m + j.val < l := by have := j.isLt; omega
        simp [red03Decode, red03Encode, futureBlock, hk0, hk1, hk2, hk3]
      · funext j
        have hk0 : ¬ (l + j.val < i.val) := by omega
        have hk1 : l + j.val ≠ i.val := by omega
        have hk2 : ¬ (l + j.val < m) := by omega
        have hk3 : ¬ (l + j.val < l) := by omega
        simp [red03Decode, red03Encode, red03Tail, hk0, hk1, hk2, hk3]

private def red03CoordEquiv {E : Type} {T m l : ℕ} (i : Fin T)
    (hi : i.val < m) (hm : m ≤ l) (hl : l ≤ T) :
    ((Fin (m-1) → E) × (E × ((Fin (l-m) → E) × (Fin (T-l) → E)))) ≃ (Fin T → E) where
  toFun := red03Encode i hi hm hl
  invFun := fun x => red03Decode x i hi hm hl
  left_inv := fun p => red03DecodeEncode i hi hm hl p
  right_inv := fun x => red03EncodeDecode i hi hm hl x

private theorem red03UniformMeanConst {A : Type} [Fintype A] [Nonempty A] (c : ℝ) :
    uniformMean (fun _ : A => c) = c := by
  simp [uniformMean]

private theorem red03ProductFubini
    (hpre : ThresholdFoundations.PreFiniteLawsStatement.{0,0})
    {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A × B → ℝ) :
    uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a,b))) :=
  hpre.2.1 A B f

theorem S4_RED_03Statement_of_deps
    (hpre : ThresholdFoundations.PreFiniteLawsStatement.{0,0}) :
    ThLean.BP.S4.S4_RED_03Statement := by
  intro E _ _ T m l i hi hm hl F
  let A := Fin (m-1) → E
  let B := Fin (l-m) → E
  let C := Fin (T-l) → E
  let P := A × (E × (B × C))
  let f : P → ℝ := fun p => F p.1 p.2.1 p.2.2.1
  let e : P ≃ (Fin T → E) := red03CoordEquiv (E := E) i hi hm hl
  have hneC : Nonempty C := inferInstance
  have hneP : Nonempty P := inferInstance
  have hneX : Nonempty (Fin T → E) := inferInstance
  have hconst : ∀ a e' b, uniformMean (fun _ : C => F a e' b) = F a e' b :=
    fun a e' b => red03UniformMeanConst (F a e' b)
  have hTarget : uniformMean (fun p : P => f p) =
      uniformMean (fun a => uniformMean (fun e' => uniformMean (fun b => F a e' b))) := by
    change uniformMean (fun p : A × (E × (B × C)) =>
      F p.1 p.2.1 p.2.2.1) = _
    rw [red03ProductFubini hpre (A := A) (B := E × (B × C))]
    have hInner : ∀ a : A,
        uniformMean (fun z : E × (B × C) => F a z.1 z.2.1) =
          uniformMean (fun e' => uniformMean (fun bc : B × C => F a e' bc.1)) := by
      intro a
      exact red03ProductFubini hpre (A := E) (B := B × C) (fun z => F a z.1 z.2.1)
    simp_rw [hInner]
    have hBC : ∀ a : A, ∀ e' : E,
        uniformMean (fun bc : B × C => F a e' bc.1) =
          uniformMean (fun b => F a e' b) := by
      intro a e'
      rw [red03ProductFubini hpre (A := B) (B := C) (fun bc => F a e' bc.1)]
      simp_rw [hconst]
      rfl
    simp_rw [hBC]
    rfl
  rw [← hTarget]
  have hReindex' : uniformMean (fun x : Fin T → E => f (e.symm x)) = uniformMean f := by
    simpa [Function.comp_def] using hpre.1 (Fin T → E) P e.symm f
  have hLeft : (fun x : Fin T → E =>
      F (omitBlock x i m hi (le_trans hm hl)) (x i) (futureBlock x m l hm hl)) =
      fun x => f (e.symm x) := by
    funext x
    simp [f, e, red03CoordEquiv, red03Decode]
  rw [hLeft, hReindex']

end ThLean.W.S415
