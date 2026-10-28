import ThLean.W.S369S.TripleLists

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
namespace ThLean.W.S369S
open ThresholdFoundations ThLean.BP.S3
variable {V : Type u} [Fintype V]

theorem pathInterior_avoid {G : MGraph V} (p : OccurrencePath G) (a b : V)
    (hp : PathFrom p a b) : a ∉ pathInterior p ∧ b ∉ pathInterior p := by
  constructor
  · intro h
    obtain ⟨i, hi, _, he⟩ := (mem_pathInterior p a).mp h
    have he' := congrArg Fin.val (p.vertex_injective (he.trans hp.1.symm))
    dsimp at he'
    omega
  · intro h
    obtain ⟨i, _, hi, he⟩ := (mem_pathInterior p b).mp h
    have he' := congrArg Fin.val (p.vertex_injective (he.trans hp.2.symm))
    dsimp at he'
    omega

theorem pathInterior_subset {G : MGraph V} (p : OccurrencePath G) {t : V}
    (ht : t ∈ pathInterior p) : t ∈ pathVertices p := by
  obtain ⟨i, _, _, hi⟩ := (mem_pathInterior p t).mp ht
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩

theorem pathInterior_disjoint {G : MGraph V} (p r : OccurrencePath G) (a b : V)
    (hp : PathFrom p a b) (hpr : pathVertices p ∩ pathVertices r ⊆ {a,b}) :
    List.Disjoint (pathInterior p) (pathInterior r) := by
  intro t ht hu
  have hm := hpr (Finset.mem_inter.mpr ⟨pathInterior_subset p ht, pathInterior_subset r hu⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with he | he
  · exact (pathInterior_avoid p a b hp).1 (he ▸ ht)
  · exact (pathInterior_avoid p a b hp).2 (he ▸ ht)

theorem labels_of_paths_nodup {G : MGraph V} (p r s : OccurrencePath G) (a b : V)
    (hab : a ≠ b) (hp : PathFrom p a b) (hr : PathFrom r a b) (hs : PathFrom s a b)
    (hpr : pathVertices p ∩ pathVertices r ⊆ {a,b})
    (hps : pathVertices p ∩ pathVertices s ⊆ {a,b})
    (hrs : pathVertices r ∩ pathVertices s ⊆ {a,b}) :
    (thetaLabels a b (pathInterior p) (pathInterior r) (pathInterior s)).Nodup := by
  have hpx := pathInterior_avoid p a b hp
  have hrx := pathInterior_avoid r a b hr
  have hsx := pathInterior_avoid s a b hs
  have dpr := pathInterior_disjoint p r a b hp hpr
  have dps := pathInterior_disjoint p s a b hp hps
  have drs := pathInterior_disjoint r s a b hr hrs
  simp only [thetaLabels, List.nodup_append', List.disjoint_append_left,
    List.disjoint_cons_left, List.disjoint_nil_left, and_true]
  exact ⟨⟨⟨by simp [hab], pathInterior_nodup p, hpx.1, hpx.2⟩,
    pathInterior_nodup r, ⟨hrx.1, hrx.2⟩, dpr⟩,
    pathInterior_nodup s, ⟨⟨hsx.1, hsx.2⟩, dps⟩, drs⟩

theorem graph_from_three_paths {G : MGraph V} (p r s : OccurrencePath G) (a b : V)
    (hp : 1 ≤ p.length) (hr : 1 ≤ r.length) (hs : 1 ≤ s.length)
    (hpa : PathFrom p a b) (hra : PathFrom r a b) (hsa : PathFrom s a b)
    (dpr : Disjoint (pathOccurrences p) (pathOccurrences r))
    (dps : Disjoint (pathOccurrences p) (pathOccurrences s))
    (drs : Disjoint (pathOccurrences r) (pathOccurrences s))
    (hcov : pathOccurrences p ∪ pathOccurrences r ∪ pathOccurrences s = Finset.univ) :
    G = thetaLists a b (pathInterior p) (pathInterior r) (pathInterior s) := by
  let xs := List.ofFn p.edge ++ List.ofFn r.edge ++ List.ofFn s.edge
  have hn : xs.Nodup := by
    simp only [xs, List.nodup_append', List.disjoint_append_left, List.nodup_ofFn]
    refine ⟨⟨p.edge_injective, r.edge_injective, ?_⟩, s.edge_injective, ?_, ?_⟩
    · intro o ho hu
      simp only [List.mem_ofFn] at ho hu
      exact Finset.disjoint_left.mp dpr
        (Finset.mem_image.mpr ⟨ho.choose, Finset.mem_univ _, ho.choose_spec⟩)
        (Finset.mem_image.mpr ⟨hu.choose, Finset.mem_univ _, hu.choose_spec⟩)
    · intro o ho hu
      simp only [List.mem_ofFn] at ho hu
      exact Finset.disjoint_left.mp dps
        (Finset.mem_image.mpr ⟨ho.choose, Finset.mem_univ _, ho.choose_spec⟩)
        (Finset.mem_image.mpr ⟨hu.choose, Finset.mem_univ _, hu.choose_spec⟩)
    · intro o ho hu
      simp only [List.mem_ofFn] at ho hu
      exact Finset.disjoint_left.mp drs
        (Finset.mem_image.mpr ⟨ho.choose, Finset.mem_univ _, ho.choose_spec⟩)
        (Finset.mem_image.mpr ⟨hu.choose, Finset.mem_univ _, hu.choose_spec⟩)
  have hu : xs.toFinset = Finset.univ := by
    have hf {n : ℕ} (f : Fin n → Occurrence G) :
        (List.ofFn f).toFinset = Finset.univ.image f := by ext o; simp
    simpa only [xs, List.toFinset_append, hf, pathOccurrences] using hcov
  have hgraph := graph_of_occurrence_list xs hn hu
  have hpath (t : OccurrencePath G) :
      (List.ofFn t.edge).map Sigma.fst = consecutiveEdges (List.ofFn t.vertex) := by
    rw [consecutiveEdges_ofFn, List.map_ofFn]
    congr 1
    funext i
    exact t.joins i
  rw [show xs.map Sigma.fst = (List.ofFn p.edge).map Sigma.fst ++
      (List.ofFn r.edge).map Sigma.fst ++ (List.ofFn s.edge).map Sigma.fst by
        simp [xs]] at hgraph
  rw [hpath p, hpath r, hpath s, path_list p a b hp hpa,
    path_list r a b hr hra, path_list s a b hs hsa] at hgraph
  exact hgraph.symm

theorem exactTheta_lists {G : MGraph V} (hG : ExactTheta G) :
    ∃ (a b : V) (x y z : List V), (thetaLabels a b x y z).Nodup ∧
      G = thetaLists a b x y z := by
  obtain ⟨a, b, hab, p, r, s, hpaths, hpair, hcov⟩ := hG
  have hp := hpaths p (by simp)
  have hr := hpaths r (by simp)
  have hs := hpaths s (by simp)
  have hpairs :
      (Disjoint (pathOccurrences p) (pathOccurrences r) ∧ pathVertices p ∩ pathVertices r ⊆ {a,b}) ∧
      (Disjoint (pathOccurrences p) (pathOccurrences s) ∧ pathVertices p ∩ pathVertices s ⊆ {a,b}) ∧
      (Disjoint (pathOccurrences r) (pathOccurrences s) ∧ pathVertices r ∩ pathVertices s ⊆ {a,b}) := by
    simpa [List.pairwise_cons, and_assoc] using hpair
  refine ⟨a, b, pathInterior p, pathInterior r, pathInterior s, ?_, ?_⟩
  · exact labels_of_paths_nodup p r s a b hab hp.2 hr.2 hs.2
      hpairs.1.2 hpairs.2.1.2 hpairs.2.2.2
  · exact graph_from_three_paths p r s a b hp.1 hr.1 hs.1 hp.2 hr.2 hs.2
      hpairs.1.1 hpairs.2.1.1 hpairs.2.2.1 hcov

end ThLean.W.S369S
