import ThLean.BP.S3.Adapters

noncomputable section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
set_option linter.style.haveILetI false

namespace ThLean.W.S391
open ThresholdFoundations
universe u

def sym2Equiv {X Y : Type*} (e : X ≃ Y) : Sym2 X ≃ Sym2 Y where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv := by intro x; simp [Sym2.map_map]
  right_inv := by intro y; simp [Sym2.map_map]

def pairEquiv {X Y : Type*} (e : X ≃ Y) : Pair X ≃ Pair Y where
  toFun p := ⟨Sym2.map e p.1, by
    intro y hy
    have heq : Sym2.map e p.1 = Sym2.map e (s(e.symm y, e.symm y)) := by simp [hy]
    have hp : p.1 = s(e.symm y, e.symm y) := (Sym2.map.injective e.injective) heq
    exact p.2 (e.symm y) hp⟩
  invFun p := ⟨Sym2.map e.symm p.1, by
    intro x hx
    have heq : Sym2.map e.symm p.1 = Sym2.map e.symm (s(e x, e x)) := by simp [hx]
    have hp : p.1 = s(e x, e x) := (Sym2.map.injective e.symm.injective) heq
    exact p.2 (e x) hp⟩
  left_inv := by intro p; apply Subtype.ext; simp [Sym2.map_map]
  right_inv := by intro p; apply Subtype.ext; simp [Sym2.map_map]

@[simp] theorem pairEquiv_val {X Y : Type*} (e : X ≃ Y) (p : Pair X) :
    (pairEquiv e p).val = Sym2.map e p.val := rfl

def edgeTupleEquiv {X Y : Type*} (e : X ≃ Y) (m : ℕ) :
    EdgeTuple X m ≃ EdgeTuple Y m where
  toFun x i := pairEquiv e (x i)
  invFun x i := pairEquiv e.symm (x i)
  left_inv := by intro x; funext i; exact (pairEquiv e).left_inv (x i)
  right_inv := by intro x; funext i; exact (pairEquiv e.symm).left_inv (x i)

theorem mapGraph_equiv_apply {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (G : MGraph X) (y : Sym2 Y) :
    mapGraph e G y = G (Sym2.map e.symm y) := by
  classical
  unfold mapGraph
  let z₀ : Sym2 X := Sym2.map e.symm y
  have hz₀ : Sym2.map e z₀ = y := by simp [z₀, Sym2.map_map]
  rw [Finset.sum_eq_single z₀]
  · simp [z₀, hz₀]
  · intro z hz hne
    have hzy : Sym2.map e z ≠ y := by
      intro heq
      apply hne
      have := congrArg (Sym2.map e.symm) heq
      simpa [z₀, Sym2.map_map] using this
    simp [hzy]
  · simp [z₀]

theorem relabel_tupleGraph {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) {m : ℕ} (x : EdgeTuple X m) :
    relabel e (tupleGraph x) = tupleGraph (edgeTupleEquiv e m x) := by
  ext y
  rw [relabel, mapGraph_equiv_apply]
  unfold tupleGraph
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (x i).val = Sym2.map e.symm y ↔ (pairEquiv e (x i)).val = y
  rw [pairEquiv_val]
  constructor
  · intro h
    have := congrArg (Sym2.map e) h
    simpa [Sym2.map_map] using this
  · intro h
    have := congrArg (Sym2.map e.symm) h
    simpa [Sym2.map_map] using this

theorem uniformMeanENN_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (f : Y → ℝ≥0∞) :
    uniformMeanENN (fun x => f (e x)) = uniformMeanENN f := by
  unfold uniformMeanENN
  rw [Fintype.sum_equiv e _ _ (by intro x; rfl), Fintype.card_congr e]

theorem poissonGraphMeanENN_relabel {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (t : ℝ) (h : MGraph Y → ℝ≥0∞) :
    poissonGraphMeanENN t (fun G => h (relabel e G)) = poissonGraphMeanENN t h := by
  unfold poissonGraphMeanENN poissonMixtureENN
  apply tsum_congr
  intro m
  change ENNReal.ofReal (poissonWeight t m) *
      uniformMeanENN (fun x => h (relabel e (tupleGraph x))) =
    ENNReal.ofReal (poissonWeight t m) *
      uniformMeanENN (fun x => h (tupleGraph x))
  congr 1
  have hfun : (fun x : EdgeTuple X m => h (relabel e (tupleGraph x))) =
      (fun x => h (tupleGraph (edgeTupleEquiv e m x))) := by
    funext x
    rw [relabel_tupleGraph]
  rw [hfun]
  apply uniformMeanENN_equiv (edgeTupleEquiv e m) (fun x => h (tupleGraph x))

def sumOptionEquiv (V : Type*) : Unit ⊕ V ≃ Option V where
  toFun := Sum.elim (fun _ => none) some
  invFun := fun x => match x with | none => Sum.inl () | some v => Sum.inr v
  left_inv := by intro x; cases x <;> simp
  right_inv := by intro x; cases x <;> simp

@[simp] theorem sumOptionEquiv_inl (V : Type*) :
    sumOptionEquiv V (Sum.inl ()) = none := rfl

@[simp] theorem sumOptionEquiv_inr (V : Type*) (v : V) :
    sumOptionEquiv V (Sum.inr v) = some v := rfl

theorem mapGraph_embedding_apply {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (hf : Function.Injective f) (G : MGraph X) (x : Sym2 X) :
    mapGraph f G (Sym2.map f x) = G x := by
  classical
  unfold mapGraph
  change (∑ y ∈ Finset.univ, (if Sym2.map f y = Sym2.map f x then G y else 0)) = G x
  calc
    (∑ y ∈ Finset.univ, (if Sym2.map f y = Sym2.map f x then G y else 0)) =
        (if Sym2.map f x = Sym2.map f x then G x else 0) := by
      apply Finset.sum_eq_single x
      · intro y hy hne
        have hneq : Sym2.map f y ≠ Sym2.map f x := by
          intro h
          apply hne
          exact (Sym2.map.injective hf) h
        simp [hneq]
      · simp
    _ = G x := by simp

@[simp] theorem mapGraph_zero {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y) :
    mapGraph f (0 : MGraph X) = 0 := by
  ext y
  simp [mapGraph]

theorem mapGraph_some_none_none {V : Type*} [Fintype V] (G : MGraph V) :
    mapGraph some G (s(none, none)) = 0 := by
  classical
  unfold mapGraph
  apply Finset.sum_eq_zero
  intro x
  induction x using Sym2.inductionOn with
  | hf a b => simp

theorem mapGraph_some_none_some {V : Type*} [Fintype V] (G : MGraph V) (v : V) :
    mapGraph some G (s(none, some v)) = 0 := by
  classical
  unfold mapGraph
  apply Finset.sum_eq_zero
  intro x
  induction x using Sym2.inductionOn with
  | hf a b => simp

@[simp] theorem mapGraph_some_some_none {V : Type*} [Fintype V] (G : MGraph V) (v : V) :
    mapGraph some G (s(some v, none)) = 0 := by
  rw [Sym2.eq_swap]
  exact mapGraph_some_none_some G v

theorem mapGraph_inr_none_none {V : Type*} [Fintype V] (G : MGraph V) :
    mapGraph (Sum.inr : V → Unit ⊕ V) G (s(Sum.inl (), Sum.inl ())) = 0 := by
  classical
  unfold mapGraph
  apply Finset.sum_eq_zero
  intro x
  induction x using Sym2.inductionOn with
  | hf a b => simp

theorem mapGraph_inr_none_some {V : Type*} [Fintype V] (G : MGraph V) (v : V) :
    mapGraph (Sum.inr : V → Unit ⊕ V) G (s(Sum.inl (), Sum.inr v)) = 0 := by
  classical
  unfold mapGraph
  apply Finset.sum_eq_zero
  intro x
  induction x using Sym2.inductionOn with
  | hf a b => simp

@[simp] theorem mapGraph_inr_some_none {V : Type*} [Fintype V] (G : MGraph V) (v : V) :
    mapGraph (Sum.inr : V → Unit ⊕ V) G (s(Sum.inr v, Sum.inl ())) = 0 := by
  rw [Sym2.eq_swap]
  exact mapGraph_inr_none_some G v

@[simp] theorem mapGraph_inr_inr {V : Type*} [Fintype V] (G : MGraph V) (a b : V) :
    mapGraph (Sum.inr : V → Unit ⊕ V) G (s(Sum.inr a, Sum.inr b)) = G (s(a, b)) := by
  simpa using mapGraph_embedding_apply (Sum.inr : V → Unit ⊕ V)
    (fun a b h => Sum.inr.inj h) G (s(a, b))

@[simp] theorem mapGraph_some_some {V : Type*} [Fintype V] (G : MGraph V) (a b : V) :
    mapGraph some G (s(some a, some b)) = G (s(a, b)) := by
  simpa using mapGraph_embedding_apply some (fun a b h => Option.some.inj h) G (s(a, b))

@[simp] theorem crossList_count {V : Type*} (xs : List V) (v : V) :
    (xs.map (fun b => s(Sum.inl (), Sum.inr b))).count (s(Sum.inl (), Sum.inr v)) =
      xs.count v := by
  exact List.count_map_of_injective xs (fun b => s(Sum.inl (), Sum.inr b))
    (by
      intro a b h
      have hh := (Sym2.eq_iff).mp h
      rcases hh with ⟨_, hb⟩ | ⟨hbad, _⟩
      · exact Sum.inr.inj hb
      · exact (Sum.inl_ne_inr hbad).elim) v

@[simp] theorem crossList_count_none_none {V : Type*} (xs : List V) :
    (xs.map (fun b => s(Sum.inl (), Sum.inr b))).count (s(Sum.inl (), Sum.inl ())) = 0 := by
  apply List.count_eq_zero_of_not_mem
  simp only [List.mem_map]
  rintro ⟨v, hv, heq⟩
  have hh := (Sym2.eq_iff).mp heq
  rcases hh with ⟨_, hbad⟩ | ⟨_, hbad⟩
  · exact (Sum.inr_ne_inl hbad).elim
  · exact (Sum.inr_ne_inl hbad).elim

@[simp] theorem crossList_count_inr_inr {V : Type*} (xs : List V) (a b : V) :
    (xs.map (fun b => s(Sum.inl (), Sum.inr b))).count (s(Sum.inr a, Sum.inr b)) = 0 := by
  apply List.count_eq_zero_of_not_mem
  simp only [List.mem_map]
  rintro ⟨v, hv, heq⟩
  have hh := (Sym2.eq_iff).mp heq
  rcases hh with ⟨hbad, _⟩ | ⟨hbad, _⟩
  · exact (Sum.inl_ne_inr hbad).elim
  · exact (Sum.inl_ne_inr hbad).elim

@[simp] theorem star_count_none_none {V : Type*} (xs : List V) :
    ThresholdFoundations.star xs (s(none, none)) = 0 := by
  unfold ThresholdFoundations.star
  apply List.count_eq_zero_of_not_mem
  simp only [List.mem_map]
  rintro ⟨v, hv, heq⟩
  have hh := (Sym2.eq_iff).mp heq
  rcases hh with ⟨_, hbad⟩ | ⟨_, hbad⟩
  · exact (Option.some_ne_none v hbad).elim
  · exact (Option.some_ne_none v hbad).elim

@[simp] theorem star_count_none_some {V : Type*} (xs : List V) (v : V) :
    ThresholdFoundations.star xs (s(none, some v)) = xs.count v := by
  unfold ThresholdFoundations.star
  exact List.count_map_of_injective xs (fun v => s(none, some v))
    (by
      intro a b h
      have hh := (Sym2.eq_iff).mp h
      rcases hh with ⟨_, hb⟩ | ⟨hbad, _⟩
      · exact Option.some.inj hb
      · exact ((Option.some_ne_none b).symm hbad).elim) v

theorem mapGraph_sumInr_relabel {V : Type*} [Fintype V] (G : MGraph V)
    (z : Sym2 (Option V)) :
    mapGraph (Sum.inr : V → Unit ⊕ V) G (Sym2.map (sumOptionEquiv V).symm z) =
      mapGraph some G z := by
  induction z using Sym2.inductionOn with
  | hf a b =>
    cases a <;> cases b <;>
      simp [sumOptionEquiv, mapGraph_inr_none_none, mapGraph_inr_none_some,
        mapGraph_inr_some_none, mapGraph_inr_inr, mapGraph_some_none_none,
        mapGraph_some_none_some, mapGraph_some_some_none, mapGraph_some_some]

theorem crossListGraph_relabel {V : Type*} (u : Unit) (xs : List V) (z : Sym2 (Option V)) :
    (xs.map (fun b => s(Sum.inl u, Sum.inr b))).count
        (Sym2.map (sumOptionEquiv V).symm z) = ThresholdFoundations.star xs z := by
  let e := sumOptionEquiv V
  let cross := fun b : V => s(Sum.inl u, Sum.inr b)
  let rooted := fun b : V => s(none, some b)
  cases u
  have hmap : (xs.map cross).map (Sym2.map e) = xs.map rooted := by
    simp [cross, rooted, e, sumOptionEquiv, List.map_map]
  have hcount := List.count_map_of_injective (xs.map cross) (Sym2.map e)
    (Sym2.map.injective e.injective) (Sym2.map e.symm z)
  simpa [e, Sym2.map_map, ThresholdFoundations.star, hmap] using hcount.symm

theorem relabel_splitUnionGraph_unit {V : Type*} [Fintype V]
    (B : MGraph V) (xs : List V) :
    relabel (sumOptionEquiv V) (splitUnionGraph (0 : MGraph Unit) B (fun _ : Unit => xs)) =
      addRoot B xs := by
  classical
  ext z
  change mapGraph (sumOptionEquiv V)
    (splitUnionGraph (0 : MGraph Unit) B (fun _ : Unit => xs)) z = addRoot B xs z
  rw [mapGraph_equiv_apply]
  simp only [splitUnionGraph, Pi.add_apply, mapGraph_zero]
  rw [Fintype.sum_unique]
  simp only [Pi.zero_apply, zero_add]
  rw [mapGraph_sumInr_relabel B z]
  unfold addRoot
  simp only [Pi.add_apply]
  apply congrArg (fun n : ℕ => mapGraph some B z + n)
  let e := sumOptionEquiv V
  let cross : V → Sym2 (Unit ⊕ V) := fun b => s(Sum.inl (default : Unit), Sum.inr b)
  let rooted : V → Sym2 (Option V) := fun b => s(none, some b)
  have hmap : (xs.map cross).map (Sym2.map e) = xs.map rooted := by
    have hu : (default : Unit) = () := Subsingleton.elim _ _
    simp [cross, rooted, e, hu, sumOptionEquiv, List.map_map]
  letI : DecidableEq Unit := Classical.decEq Unit
  have hcount := List.count_map_of_injective (xs.map cross) (Sym2.map e)
    (Sym2.map.injective e.injective) (Sym2.map e.symm z)
  simpa [e, Sym2.map_map, ThresholdFoundations.star, hmap] using hcount.symm

theorem poissonGraphMeanENN_zero_unit (f : MGraph Unit → ℝ≥0∞) :
    poissonGraphMeanENN 0 f = f 0 := by
  unfold poissonGraphMeanENN poissonMixtureENN
  rw [tsum_eq_single 0]
  · simp [poissonWeight, uniformMeanENN]
    congr 1
  · intro m hm
    simp [poissonWeight, hm]

def unitArrayEquiv (V : Type*) (n : ℕ) :
    (Unit → Fin n → V) ≃ (Fin n → V) := Equiv.funUnique Unit (Fin n → V)

set_option maxHeartbeats 1000000 in
theorem independentPoissonListsMeanENN_unit {V : Type*} [Fintype V]
    (z : ℝ) (f : List V → ℝ≥0∞) :
    independentPoissonListsMeanENN z (fun xs : Unit → List V => f (xs ())) =
      uniformPoissonListMeanENN z f := by
  unfold independentPoissonListsMeanENN uniformPoissonListMeanENN poissonMixtureENN
  dsimp
  letI : DecidableEq Unit := Classical.decEq Unit
  calc
    (∑' k : Unit → ℕ,
        (∏ a : Unit, ENNReal.ofReal (poissonWeight z (k a))) *
          uniformMeanENN (fun x : (a : Unit) → Fin (k a) → V =>
            f (List.ofFn (x ())))) =
      ∑' n : ℕ,
        (∏ a : Unit, ENNReal.ofReal
          (poissonWeight z (((Equiv.funUnique Unit ℕ).symm n) a))) *
          uniformMeanENN (fun x : (a : Unit) →
            Fin (((Equiv.funUnique Unit ℕ).symm n) a) → V => f (List.ofFn (x ()))) :=
      (Equiv.tsum_eq (Equiv.funUnique Unit ℕ).symm (fun k : Unit → ℕ =>
        (∏ a : Unit, ENNReal.ofReal (poissonWeight z (k a))) *
          uniformMeanENN (fun x : (a : Unit) → Fin (k a) → V =>
            f (List.ofFn (x ()))))).symm
    _ = ∑' n : ℕ, ENNReal.ofReal (poissonWeight z n) *
          uniformMeanENN (fun x : Fin n → V => f (List.ofFn x)) := by
      apply tsum_congr
      intro n
      have hmean :
          uniformMeanENN (fun x : Unit → Fin n → V => f (List.ofFn (x ()))) =
            uniformMeanENN (fun x : Fin n → V => f (List.ofFn x)) := by
        simpa [unitArrayEquiv, Equiv.funUnique] using
          (uniformMeanENN_equiv (unitArrayEquiv V n)
            (fun x : Fin n → V => f (List.ofFn x)))
      simp only [Equiv.funUnique, Fintype.prod_unique]
      exact congrArg (fun y : ℝ≥0∞ => ENNReal.ofReal (poissonWeight z n) * y) hmean

end ThLean.W.S391
