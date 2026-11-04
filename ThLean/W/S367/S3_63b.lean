module

public import ThLean.BP.S3.Cycles

@[expose] public section

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
namespace ThLean.W.S367
open ThresholdFoundations ThLean.BP.S3
universe u

private def selectedAt {V : Type u} [Fintype V] {G : MGraph V}
    (U : Finset (Occurrence G)) (e : Sym2 V) : Finset (Fin (G e)) :=
  Finset.univ.filter (fun i => (⟨e, i⟩ : Occurrence G) ∈ U)

private def compactGraph {V : Type u} [Fintype V] {G : MGraph V}
    (U : Finset (Occurrence G)) : MGraph V :=
  fun e => (selectedAt U e).card

private theorem compactGraph_sub {V : Type u} [Fintype V] {G : MGraph V}
    (U : Finset (Occurrence G)) : subgraph (compactGraph U) G := by
  intro e
  calc
    (selectedAt U e).card ≤ (Finset.univ : Finset (Fin (G e))).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = G e := by simp

private noncomputable def compactOccurrence {V : Type u} [Fintype V] {G : MGraph V}
    {U : Finset (Occurrence G)} (o : Occurrence G) (ho : o ∈ U) :
    Occurrence (compactGraph U) := by
  let S := selectedAt U o.1
  have hmem : o.2 ∈ S := by simp [S, selectedAt, ho]
  refine ⟨o.1, ?_⟩
  change Fin S.card
  exact (S.orderIsoOfFin rfl).symm ⟨o.2, hmem⟩

private noncomputable def uncompactOccurrence {V : Type u} [Fintype V] {G : MGraph V}
    (U : Finset (Occurrence G)) (o : Occurrence (compactGraph U)) : Occurrence G :=
  ⟨o.1, (selectedAt U o.1).orderEmbOfFin rfl o.2⟩

private theorem uncompact_compactOccurrence {V : Type u} [Fintype V] {G : MGraph V}
    {U : Finset (Occurrence G)} (o : Occurrence G) (ho : o ∈ U) :
    uncompactOccurrence U (compactOccurrence o ho) = o := by
  cases o with
  | mk e i =>
    dsimp [uncompactOccurrence, compactOccurrence]
    apply Sigma.ext
    · rfl
    ·
      let S := selectedAt U e
      have hmem : i ∈ S := by simp [S, selectedAt, ho]
      have hidx : S.orderEmbOfFin rfl ((S.orderIsoOfFin rfl).symm ⟨i, hmem⟩) = i := by
        rw [Finset.orderEmbOfFin]
        exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨i, hmem⟩)
      exact heq_of_eq hidx

private theorem compactOccurrence_injective {V : Type u} [Fintype V] {G : MGraph V}
    {U : Finset (Occurrence G)} {o o' : Occurrence G} (ho : o ∈ U) (ho' : o' ∈ U)
    (h : compactOccurrence o ho = compactOccurrence o' ho') : o = o' := by
  have hh := congrArg (uncompactOccurrence U) h
  rw [uncompact_compactOccurrence o ho, uncompact_compactOccurrence o' ho'] at hh
  exact hh

private theorem compactOccurrence_congr {V : Type u} [Fintype V] {G : MGraph V}
    {U : Finset (Occurrence G)} {o o' : Occurrence G} (ho : o ∈ U) (ho' : o' ∈ U)
    (h : o = o') : compactOccurrence o ho = compactOccurrence o' ho' := by
  subst o'
  have : ho = ho' := Subsingleton.elim _ _
  subst ho'
  rfl

private theorem uncompact_mem {V : Type u} [Fintype V] {G : MGraph V}
    (U : Finset (Occurrence G)) (o : Occurrence (compactGraph U)) :
    uncompactOccurrence U o ∈ U := by
  have hm := Finset.orderEmbOfFin_mem (selectedAt U o.1) rfl o.2
  simpa [uncompactOccurrence, selectedAt] using hm

private theorem compact_uncompactOccurrence {V : Type u} [Fintype V] {G : MGraph V}
    (U : Finset (Occurrence G)) (o : Occurrence (compactGraph U))
    (ho : uncompactOccurrence U o ∈ U) :
    compactOccurrence (uncompactOccurrence U o) ho = o := by
  cases o with
  | mk e i =>
    dsimp [uncompactOccurrence, compactOccurrence]
    apply Sigma.ext
    · rfl
    ·
      let S := selectedAt U e
      have hmem := Finset.orderEmbOfFin_mem S rfl i
      have hidx : (S.orderIsoOfFin rfl) i =
          ⟨S.orderEmbOfFin rfl i, hmem⟩ := by
        apply Subtype.ext
        exact Finset.coe_orderIsoOfFin_apply S rfl i
      have hsymm := congrArg (S.orderIsoOfFin rfl).symm hidx
      have hEq : (S.orderIsoOfFin rfl).symm ⟨S.orderEmbOfFin rfl i, hmem⟩ = i := by
        exact hsymm.symm.trans ((S.orderIsoOfFin rfl).symm_apply_apply i)
      exact heq_of_eq hEq

private noncomputable def compactPath {V : Type u} [Fintype V] {G : MGraph V}
    {U : Finset (Occurrence G)} (p : OccurrencePath G)
    (hp : ∀ i, p.edge i ∈ U) : OccurrencePath (compactGraph U) :=
  { length := p.length
    vertex := p.vertex
    edge := fun i => compactOccurrence (p.edge i) (hp i)
    vertex_injective := p.vertex_injective
    edge_injective := by
      intro i j hij
      apply p.edge_injective
      exact compactOccurrence_injective (hp i) (hp j) hij
    joins := by
      intro i
      exact p.joins i }

private noncomputable def compactCycle {V : Type u} [Fintype V] {G : MGraph V}
    {U : Finset (Occurrence G)} (c : OccurrenceCycle G)
    (hc : ∀ i, c.edge i ∈ U) : OccurrenceCycle (compactGraph U) :=
  { length := c.length
    length_ge_two := c.length_ge_two
    vertex := c.vertex
    edge := fun i => compactOccurrence (c.edge i) (hc i)
    vertex_injective := c.vertex_injective
    edge_injective := by
      intro i j hij
      apply c.edge_injective
      exact compactOccurrence_injective (hc i) (hc j) hij
    joins := by
      intro i
      exact c.joins i }

private theorem compactPath_occurrences {V : Type u} [Fintype V] {G : MGraph V}
    {U : Finset (Occurrence G)} (p : OccurrencePath G) (hp : ∀ i, p.edge i ∈ U) :
    pathOccurrences (compactPath p hp) =
      Finset.univ.image (fun i => compactOccurrence (p.edge i) (hp i)) := rfl

private theorem compactCycle_occurrences {V : Type u} [Fintype V] {G : MGraph V}
    {U : Finset (Occurrence G)} (c : OccurrenceCycle G) (hc : ∀ i, c.edge i ∈ U) :
    cycleOccurrences (compactCycle c hc) =
      Finset.univ.image (fun i => compactOccurrence (c.edge i) (hc i)) := rfl

private theorem compactPath_disjoint {V : Type u} [Fintype V] {G : MGraph V}
    {U : Finset (Occurrence G)} (p r : OccurrencePath G)
    (hp : ∀ i, p.edge i ∈ U) (hr : ∀ i, r.edge i ∈ U)
    (hdisj : Disjoint (pathOccurrences p) (pathOccurrences r)) :
    Disjoint (pathOccurrences (compactPath p hp)) (pathOccurrences (compactPath r hr)) := by
  rw [compactPath_occurrences, compactPath_occurrences]
  apply Finset.disjoint_left.mpr
  intro x hxP hxR
  rcases Finset.mem_image.mp hxP with ⟨i, -, rfl⟩
  rcases Finset.mem_image.mp hxR with ⟨j, -, hij⟩
  have heq := compactOccurrence_injective (hp i) (hr j) hij.symm
  exact (Finset.disjoint_left.mp hdisj) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq.symm⟩)

private theorem compactCycle_disjoint {V : Type u} [Fintype V] {G : MGraph V}
    {U : Finset (Occurrence G)} (c d : OccurrenceCycle G)
    (hc : ∀ i, c.edge i ∈ U) (hd : ∀ i, d.edge i ∈ U)
    (hdisj : Disjoint (cycleOccurrences c) (cycleOccurrences d)) :
    Disjoint (cycleOccurrences (compactCycle c hc)) (cycleOccurrences (compactCycle d hd)) := by
  rw [compactCycle_occurrences, compactCycle_occurrences]
  apply Finset.disjoint_left.mpr
  intro x hxC hxD
  rcases Finset.mem_image.mp hxC with ⟨i, -, rfl⟩
  rcases Finset.mem_image.mp hxD with ⟨j, -, hij⟩
  have heq := compactOccurrence_injective (hc i) (hd j) hij.symm
  exact (Finset.disjoint_left.mp hdisj) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq.symm⟩)

private theorem compactPath_contains_uncompact {V : Type u} [Fintype V] {G : MGraph V}
    {U : Finset (Occurrence G)} (p : OccurrencePath G) (hp : ∀ i, p.edge i ∈ U)
    (x : Occurrence (compactGraph U))
    (h : uncompactOccurrence U x ∈ pathOccurrences p) :
    x ∈ pathOccurrences (compactPath p hp) := by
  rcases Finset.mem_image.mp h with ⟨i, -, hi⟩
  have hx := compact_uncompactOccurrence U x (uncompact_mem U x)
  have hx' := (compactOccurrence_congr (hp i) (uncompact_mem U x) hi).trans hx
  rw [compactPath_occurrences]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hx'⟩

private theorem compactCycle_contains_uncompact {V : Type u} [Fintype V] {G : MGraph V}
    {U : Finset (Occurrence G)} (c : OccurrenceCycle G) (hc : ∀ i, c.edge i ∈ U)
    (x : Occurrence (compactGraph U))
    (h : uncompactOccurrence U x ∈ cycleOccurrences c) :
    x ∈ cycleOccurrences (compactCycle c hc) := by
  rcases Finset.mem_image.mp h with ⟨i, -, hi⟩
  have hx := compact_uncompactOccurrence U x (uncompact_mem U x)
  have hx' := (compactOccurrence_congr (hc i) (uncompact_mem U x) hi).trans hx
  rw [compactCycle_occurrences]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hx'⟩

private theorem compactPath_triple_cover {V : Type u} [Fintype V] {G : MGraph V}
    {U : Finset (Occurrence G)} (p r s : OccurrencePath G)
    (hp : ∀ i, p.edge i ∈ U) (hr : ∀ i, r.edge i ∈ U) (hs : ∀ i, s.edge i ∈ U)
    (hU : U = pathOccurrences p ∪ pathOccurrences r ∪ pathOccurrences s) :
    pathOccurrences (compactPath p hp) ∪ pathOccurrences (compactPath r hr) ∪
      pathOccurrences (compactPath s hs) = Finset.univ := by
  subst U
  ext x
  constructor
  · intro _
    simp
  · intro _
    have hxU := uncompact_mem _ x
    rcases Finset.mem_union.mp hxU with hpr | hs'
    · rcases Finset.mem_union.mp hpr with hp' | hr'
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inl (compactPath_contains_uncompact p hp x hp'))))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inr (compactPath_contains_uncompact r hr x hr'))))
    · exact Finset.mem_union.mpr (Or.inr (compactPath_contains_uncompact s hs x hs'))

private theorem compactCycle_pair_cover {V : Type u} [Fintype V] {G : MGraph V}
    {U : Finset (Occurrence G)} (c d : OccurrenceCycle G)
    (hc : ∀ i, c.edge i ∈ U) (hd : ∀ i, d.edge i ∈ U)
    (hU : U = cycleOccurrences c ∪ cycleOccurrences d) :
    cycleOccurrences (compactCycle c hc) ∪ cycleOccurrences (compactCycle d hd) = Finset.univ := by
  subst U
  ext x
  constructor
  · intro _
    simp
  · intro _
    have hxU := uncompact_mem _ x
    rcases Finset.mem_union.mp hxU with hc' | hd'
    · exact Finset.mem_union.mpr (Or.inl (compactCycle_contains_uncompact c hc x hc'))
    · exact Finset.mem_union.mpr (Or.inr (compactCycle_contains_uncompact d hd x hd'))

private theorem compactCyclesPath_cover {V : Type u} [Fintype V] {G : MGraph V}
    {U : Finset (Occurrence G)} (c d : OccurrenceCycle G) (p : OccurrencePath G)
    (hc : ∀ i, c.edge i ∈ U) (hd : ∀ i, d.edge i ∈ U) (hp : ∀ i, p.edge i ∈ U)
    (hU : U = cycleOccurrences c ∪ cycleOccurrences d ∪ pathOccurrences p) :
    cycleOccurrences (compactCycle c hc) ∪ cycleOccurrences (compactCycle d hd) ∪
      pathOccurrences (compactPath p hp) = Finset.univ := by
  subst U
  ext x
  constructor
  · intro _
    simp
  · intro _
    have hxU := uncompact_mem _ x
    rcases Finset.mem_union.mp hxU with hcd | hp'
    · rcases Finset.mem_union.mp hcd with hc' | hd'
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inl (compactCycle_contains_uncompact c hc x hc'))))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inr (compactCycle_contains_uncompact d hd x hd'))))
    · exact Finset.mem_union.mpr (Or.inr (compactPath_contains_uncompact p hp x hp'))

private theorem compactPath_disjoint_cycles {V : Type u} [Fintype V] {G : MGraph V}
    {U : Finset (Occurrence G)} (p : OccurrencePath G) (c d : OccurrenceCycle G)
    (hp : ∀ i, p.edge i ∈ U) (hc : ∀ i, c.edge i ∈ U) (hd : ∀ i, d.edge i ∈ U)
    (hdisj : Disjoint (pathOccurrences p) (cycleOccurrences c ∪ cycleOccurrences d)) :
    Disjoint (pathOccurrences (compactPath p hp))
      (cycleOccurrences (compactCycle c hc) ∪ cycleOccurrences (compactCycle d hd)) := by
  rw [compactPath_occurrences, compactCycle_occurrences, compactCycle_occurrences]
  apply Finset.disjoint_left.mpr
  intro x hxp hxcd
  rcases Finset.mem_image.mp hxp with ⟨i, -, rfl⟩
  rcases Finset.mem_union.mp hxcd with hxc | hxd
  · rcases Finset.mem_image.mp hxc with ⟨j, -, hij⟩
    have heq := compactOccurrence_injective (hp i) (hc j) hij.symm
    exact (Finset.disjoint_left.mp hdisj)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq.symm⟩)))
  · rcases Finset.mem_image.mp hxd with ⟨j, -, hij⟩
    have heq := compactOccurrence_injective (hp i) (hd j) hij.symm
    exact (Finset.disjoint_left.mp hdisj)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq.symm⟩)))

theorem S3_63bStatement_holds : ThLean.BP.S3.S3_63bStatement := by
  intro V instV G hG hstruct
  classical
  rcases hstruct with htheta | hdumb
  · rcases htheta with ⟨a, b, hab, p₁, p₂, p₃, hpaths, hpair⟩
    let U := pathOccurrences p₁ ∪ pathOccurrences p₂ ∪ pathOccurrences p₃
    let F := compactGraph U
    have hp₁ : ∀ i, p₁.edge i ∈ U := by intro i; simp [U, pathOccurrences]
    have hp₂ : ∀ i, p₂.edge i ∈ U := by intro i; simp [U, pathOccurrences]
    have hp₃ : ∀ i, p₃.edge i ∈ U := by intro i; simp [U, pathOccurrences]
    let q₁ := compactPath p₁ hp₁
    let q₂ := compactPath p₂ hp₂
    let q₃ := compactPath p₃ hp₃
    have hpaths' : ∀ q ∈ [q₁, q₂, q₃], 1 ≤ q.length ∧ PathFrom q a b := by
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with hq | hq
      · subst q
        change 1 ≤ p₁.length ∧ PathFrom p₁ a b
        exact hpaths p₁ (by simp)
      · rcases hq with hq | hq
        · subst q
          change 1 ≤ p₂.length ∧ PathFrom p₂ a b
          exact hpaths p₂ (by simp)
        · rcases hq with hq | hq
          · subst q
            change 1 ≤ p₃.length ∧ PathFrom p₃ a b
            exact hpaths p₃ (by simp)
          · simp at hq
    have hpair0 := hpair
    have hpair' : [q₁, q₂, q₃].Pairwise (fun q r =>
        Disjoint (pathOccurrences q) (pathOccurrences r) ∧
        pathVertices q ∩ pathVertices r ⊆ {a, b}) := by
      simp only [List.pairwise_cons] at hpair0 ⊢
      rcases hpair0 with ⟨h1tail, hrest⟩
      rcases hrest with ⟨h2tail, _⟩
      have h12 := h1tail p₂ (by simp)
      have h13 := h1tail p₃ (by simp)
      have h23 := h2tail p₃ (by simp)
      refine ⟨?_, ?_⟩
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with hq | hq
        · subst q
          exact ⟨compactPath_disjoint p₁ p₂ hp₁ hp₂ h12.1, by
            change pathVertices p₁ ∩ pathVertices p₂ ⊆ {a, b}
            exact h12.2⟩
        · rcases hq with hq | hq
          · subst q
            exact ⟨compactPath_disjoint p₁ p₃ hp₁ hp₃ h13.1, by
              change pathVertices p₁ ∩ pathVertices p₃ ⊆ {a, b}
              exact h13.2⟩
          · simp at hq
      · refine ⟨?_, ?_⟩
        · intro q hq
          simp only [List.mem_cons] at hq
          rcases hq with hq | hq
          · subst q
            exact ⟨compactPath_disjoint p₂ p₃ hp₂ hp₃ h23.1, by
              change pathVertices p₂ ∩ pathVertices p₃ ⊆ {a, b}
              exact h23.2⟩
          · simp at hq
        · simp
    have hcover : pathOccurrences q₁ ∪ pathOccurrences q₂ ∪ pathOccurrences q₃ = Finset.univ := by
      exact compactPath_triple_cover p₁ p₂ p₃ hp₁ hp₂ hp₃ rfl
    have hExact : ExactTheta F := by
      refine ⟨a, b, hab, q₁, q₂, q₃, hpaths', hpair', ?_⟩
      simpa [q₁, q₂, q₃, F] using hcover
    refine ⟨F, ?_, ?_, Or.inl hExact⟩
    · simpa [F] using compactGraph_sub U
    · intro v
      have hle := compactGraph_sub U (s(v,v))
      rw [hG v] at hle
      exact Nat.eq_zero_of_le_zero hle
  · rcases hdumb with ⟨c₁, c₂, hcyclesDisj, hcase⟩
    rcases hcase with hshared | ⟨hvertsDisj, p, a, b, hpPos, hpFrom, ha, hb,
      hpv₁, hpv₂, hpDisj⟩
    · let U := cycleOccurrences c₁ ∪ cycleOccurrences c₂
      let F := compactGraph U
      have hc₁ : ∀ i, c₁.edge i ∈ U := by intro i; simp [U, cycleOccurrences]
      have hc₂ : ∀ i, c₂.edge i ∈ U := by intro i; simp [U, cycleOccurrences]
      let d₁ := compactCycle c₁ hc₁
      let d₂ := compactCycle c₂ hc₂
      have hExact : ExactDumbbell F := by
        refine ⟨d₁, d₂, compactCycle_disjoint c₁ c₂ hc₁ hc₂ hcyclesDisj, Or.inl ?_⟩
        refine ⟨?_, ?_⟩
        · change (cycleVertices c₁ ∩ cycleVertices c₂).card = 1
          exact hshared
        · exact compactCycle_pair_cover c₁ c₂ hc₁ hc₂ rfl
      refine ⟨F, ?_, ?_, Or.inr hExact⟩
      · simpa [F] using compactGraph_sub U
      · intro v
        have hle := compactGraph_sub U (s(v,v))
        rw [hG v] at hle
        exact Nat.eq_zero_of_le_zero hle
    · let U := cycleOccurrences c₁ ∪ cycleOccurrences c₂ ∪ pathOccurrences p
      let F := compactGraph U
      have hc₁ : ∀ i, c₁.edge i ∈ U := by intro i; simp [U, cycleOccurrences, pathOccurrences]
      have hc₂ : ∀ i, c₂.edge i ∈ U := by intro i; simp [U, cycleOccurrences, pathOccurrences]
      have hp : ∀ i, p.edge i ∈ U := by intro i; simp [U, cycleOccurrences, pathOccurrences]
      let d₁ := compactCycle c₁ hc₁
      let d₂ := compactCycle c₂ hc₂
      let q := compactPath p hp
      have hExact : ExactDumbbell F := by
        refine ⟨d₁, d₂, compactCycle_disjoint c₁ c₂ hc₁ hc₂ hcyclesDisj, Or.inr ?_⟩
        refine ⟨?_, ⟨q, a, b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
        · change Disjoint (cycleVertices c₁) (cycleVertices c₂)
          exact hvertsDisj
        · change 1 ≤ p.length
          exact hpPos
        · change PathFrom p a b
          exact hpFrom
        · change a ∈ cycleVertices c₁
          exact ha
        · change b ∈ cycleVertices c₂
          exact hb
        · change pathVertices p ∩ cycleVertices c₁ = {a}
          exact hpv₁
        · change pathVertices p ∩ cycleVertices c₂ = {b}
          exact hpv₂
        · exact compactPath_disjoint_cycles p c₁ c₂ hp hc₁ hc₂ hpDisj
        · exact compactCyclesPath_cover c₁ c₂ p hc₁ hc₂ hp rfl
      refine ⟨F, ?_, ?_, Or.inr hExact⟩
      · simpa [F] using compactGraph_sub U
      · intro v
        have hle := compactGraph_sub U (s(v,v))
        rw [hG v] at hle
        exact Nat.eq_zero_of_le_zero hle

end ThLean.W.S367
