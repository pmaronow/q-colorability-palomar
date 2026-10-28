import ThLean.BP.S3.Adapters

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S392S
open ThresholdFoundations

variable {V : Type u} [Fintype V] {G : MGraph V} {S : Finset V}

/-- Keep the occurrence index while including an induced graph in its parent. -/
def liftOccurrence (e : Occurrence (inducedGraph G S)) : Occurrence G :=
  ⟨Sym2.map Subtype.val e.1, e.2⟩

theorem liftOccurrence_injective :
    Function.Injective (liftOccurrence (G := G) (S := S)) := by
  rintro ⟨e, i⟩ ⟨f, j⟩ h
  have hef : e = f := Sym2.map.injective Subtype.val_injective (congrArg Sigma.fst h)
  subst f
  exact congrArg (Sigma.mk e)
    (@sigma_mk_injective (Sym2 V) (fun x => Fin (G x)) (Sym2.map Subtype.val e) i j h)

def liftPath (p : OccurrencePath (inducedGraph G S)) : OccurrencePath G where
  length := p.length
  vertex := fun i => (p.vertex i).val
  edge := fun i => liftOccurrence (p.edge i)
  vertex_injective := Subtype.val_injective.comp p.vertex_injective
  edge_injective := liftOccurrence_injective.comp p.edge_injective
  joins := by
    intro i
    change Sym2.map Subtype.val (p.edge i).1 = _
    rw [p.joins i, Sym2.map_mk]

def liftCycle (c : OccurrenceCycle (inducedGraph G S)) : OccurrenceCycle G where
  length := c.length
  length_ge_two := c.length_ge_two
  vertex := fun i => (c.vertex i).val
  edge := fun i => liftOccurrence (c.edge i)
  vertex_injective := Subtype.val_injective.comp c.vertex_injective
  edge_injective := liftOccurrence_injective.comp c.edge_injective
  joins := by
    intro i
    change Sym2.map Subtype.val (c.edge i).1 = _
    rw [c.joins i, Sym2.map_mk]

@[simp] theorem pathVertices_lift (p : OccurrencePath (inducedGraph G S)) :
    pathVertices (liftPath p) = (pathVertices p).image Subtype.val := by
  simp only [pathVertices, liftPath, Finset.image_image, Function.comp_def]
  rfl

@[simp] theorem pathOccurrences_lift (p : OccurrencePath (inducedGraph G S)) :
    pathOccurrences (liftPath p) = (pathOccurrences p).image liftOccurrence := by
  simp only [pathOccurrences, liftPath, Finset.image_image, Function.comp_def]
  rfl

@[simp] theorem cycleVertices_lift (c : OccurrenceCycle (inducedGraph G S)) :
    cycleVertices (liftCycle c) = (cycleVertices c).image Subtype.val := by
  simp only [cycleVertices, liftCycle, Finset.image_image, Function.comp_def]
  rfl

@[simp] theorem cycleOccurrences_lift (c : OccurrenceCycle (inducedGraph G S)) :
    cycleOccurrences (liftCycle c) = (cycleOccurrences c).image liftOccurrence := by
  simp only [cycleOccurrences, liftCycle, Finset.image_image, Function.comp_def]
  rfl

theorem pathFrom_lift {p : OccurrencePath (inducedGraph G S)}
    {a b : {v : V // v ∈ S}} (hp : PathFrom p a b) :
    PathFrom (liftPath p) a.val b.val :=
  ⟨congrArg Subtype.val hp.1, congrArg Subtype.val hp.2⟩

theorem thetaIn_lift (h : ThetaIn (inducedGraph G S)) : ThetaIn G := by
  classical
  letI : DecidableEq {v : V // v ∈ S} := fun a b => Classical.propDecidable (a = b)
  rcases h with ⟨a, b, hab, p₁, p₂, p₃, hp, hpair⟩
  refine ⟨a.val, b.val, (fun h => hab (Subtype.ext h)),
    liftPath p₁, liftPath p₂, liftPath p₃, ?_, ?_⟩
  · intro p hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact ⟨(hp p₁ (by simp)).1, pathFrom_lift (hp p₁ (by simp)).2⟩
    · exact ⟨(hp p₂ (by simp)).1, pathFrom_lift (hp p₂ (by simp)).2⟩
    · exact ⟨(hp p₃ (by simp)).1, pathFrom_lift (hp p₃ (by simp)).2⟩
  · change ([p₁, p₂, p₃].map liftPath).Pairwise _
    apply hpair.map liftPath
    intro p r hpr
    constructor
    · simpa only [pathOccurrences_lift] using
        (Finset.disjoint_image liftOccurrence_injective).mpr hpr.1
    · rw [pathVertices_lift, pathVertices_lift,
        ← Finset.image_inter _ _ Subtype.val_injective]
      simpa using Finset.image_subset_image (f := Subtype.val) hpr.2

theorem dumbbellIn_lift (h : DumbbellIn (inducedGraph G S)) : DumbbellIn G := by
  classical
  letI : DecidableEq {v : V // v ∈ S} := fun a b => Classical.propDecidable (a = b)
  rcases h with ⟨c₁, c₂, hdisj, hmeet | ⟨hvdisj, p, a, b, hp, hab, ha, hb, hpc₁, hpc₂, hpd⟩⟩
  · refine ⟨liftCycle c₁, liftCycle c₂, ?_, Or.inl ?_⟩
    · simpa only [cycleOccurrences_lift] using
        (Finset.disjoint_image liftOccurrence_injective).mpr hdisj
    · rw [cycleVertices_lift, cycleVertices_lift,
        ← Finset.image_inter _ _ Subtype.val_injective,
        Finset.card_image_of_injective _ Subtype.val_injective]
      exact hmeet
  · refine ⟨liftCycle c₁, liftCycle c₂, ?_, Or.inr ⟨?_,
      liftPath p, a.val, b.val, hp, pathFrom_lift hab, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simpa only [cycleOccurrences_lift] using
        (Finset.disjoint_image liftOccurrence_injective).mpr hdisj
    · simpa only [cycleVertices_lift] using
        (Finset.disjoint_image Subtype.val_injective).mpr hvdisj
    · rw [cycleVertices_lift]
      exact Finset.mem_image_of_mem Subtype.val ha
    · rw [cycleVertices_lift]
      exact Finset.mem_image_of_mem Subtype.val hb
    · rw [pathVertices_lift, cycleVertices_lift,
        ← Finset.image_inter _ _ Subtype.val_injective, hpc₁, Finset.image_singleton]
    · rw [pathVertices_lift, cycleVertices_lift,
        ← Finset.image_inter _ _ Subtype.val_injective, hpc₂, Finset.image_singleton]
    · rw [pathOccurrences_lift, cycleOccurrences_lift, cycleOccurrences_lift,
        ← Finset.image_union]
      exact (Finset.disjoint_image liftOccurrence_injective).mpr hpd

end ThLean.W.S392S
