import ThLean.BP.S3.Cycles

noncomputable section
open scoped BigOperators
namespace ThLean.W.S358
open ThresholdFoundations ThLean.BP.S3
attribute [local instance] Classical.propDecidable

private def treeMGraph {V : Type*} [Fintype V] (S : SimpleGraph V) : MGraph V :=
  fun e => if e ∈ S.edgeSet then 1 else 0

private theorem graphSupport_treeMGraph {V : Type*} [Fintype V] (S : SimpleGraph V) :
    graphSupport (treeMGraph S) = S := by
  ext a b
  constructor
  · rintro ⟨hne, hpos⟩
    by_cases hadj : S.Adj a b
    · exact hadj
    · simp [graphSupport, treeMGraph, SimpleGraph.mem_edgeSet, hadj] at hpos
  · intro hadj
    exact ⟨hadj.ne, by simp [graphSupport, treeMGraph, SimpleGraph.mem_edgeSet, hadj]⟩

private theorem treeMGraph_loopless {V : Type*} [Fintype V] (S : SimpleGraph V) :
    Loopless (treeMGraph S) := by
  intro a
  simp [treeMGraph, SimpleGraph.mem_edgeSet]

private theorem treeMGraph_subgraph {V : Type*} [Fintype V] (K : MGraph V)
    (S : SimpleGraph V) (hSK : S ≤ graphSupport K) : subgraph (treeMGraph S) K := by
  intro e
  refine e.ind ?_
  intro a b
  by_cases he : s(a,b) ∈ S.edgeSet
  · have hAdj : S.Adj a b := (SimpleGraph.mem_edgeSet S).mp he
    have hK := hSK hAdj
    simpa [treeMGraph, he] using Nat.succ_le_of_lt hK.2
  · simp [treeMGraph, he]

private theorem edgeCount_treeMGraph {V : Type*} [Fintype V] (S : SimpleGraph V) :
    edgeCount (treeMGraph S) = S.edgeFinset.card := by
  classical
  have hset : Finset.univ.filter (fun e : Sym2 V => e ∈ S.edgeSet) = S.edgeFinset := by
    ext e
    simp [SimpleGraph.mem_edgeFinset]
  rw [edgeCount]
  simp only [treeMGraph]
  rw [Finset.sum_boole]
  simp [hset]

private def occurrencePathWalkAux {V : Type*} [Fintype V] (T : MGraph V)
    (S : SimpleGraph V) (hTS : graphSupport T = S) (hloop : Loopless T) :
    (n : ℕ) → (v : Fin (n + 1) → V) → (e : Fin n → Occurrence T) →
    (∀ i, (e i).1 = s(v ⟨i.val, by omega⟩, v ⟨i.val + 1, by omega⟩)) →
      S.Walk (v ⟨0, by omega⟩) (v ⟨n, by omega⟩)
  | 0, v, _, _ => SimpleGraph.Walk.nil
  | n + 1, v, e, joins => by
      let j₀ : Fin (n + 2) := ⟨0, by omega⟩
      let j₁ : Fin (n + 2) := ⟨1, by omega⟩
      let i₀ : Fin (n + 1) := ⟨0, by omega⟩
      have hTkey : T (e i₀).1 = T (s(v j₀, v j₁)) := congrArg T (joins i₀)
      have hne : v j₀ ≠ v j₁ := by
        intro hab
        have hpos : 0 < T (e i₀).1 :=
          lt_of_le_of_lt (Nat.zero_le _) (e i₀).2.isLt
        rw [hTkey] at hpos
        rw [hab] at hpos
        rw [hloop (v j₁)] at hpos
        omega
      have hpos : 0 < T (s(v j₀, v j₁)) := by
        rw [← hTkey]
        exact lt_of_le_of_lt (Nat.zero_le _) (e i₀).2.isLt
      have hAdjT : (graphSupport T).Adj (v j₀) (v j₁) := ⟨hne, hpos⟩
      have hAdj : S.Adj (v j₀) (v j₁) := by
        rw [← hTS]
        exact hAdjT
      exact SimpleGraph.Walk.cons hAdj
        (occurrencePathWalkAux T S hTS hloop n
          (fun i => v ⟨i.val + 1, by omega⟩)
          (fun i => e ⟨i.val + 1, by omega⟩)
          (by
            intro i
            simpa using joins (⟨i.val + 1, by omega⟩ : Fin (n + 1))))

private theorem occurrencePathWalkAux_length {V : Type*} [Fintype V] (T : MGraph V)
    (S : SimpleGraph V) (hTS : graphSupport T = S) (hloop : Loopless T) :
    ∀ n (v : Fin (n + 1) → V) (e : Fin n → Occurrence T) (joins),
      (occurrencePathWalkAux T S hTS hloop n v e joins).length = n := by
  intro n
  induction n with
  | zero => intro v e joins; rfl
  | succ n ih =>
      intro v e joins
      simp only [occurrencePathWalkAux, SimpleGraph.Walk.length_cons]
      congr 1
      exact ih (fun i => v ⟨i.val + 1, by omega⟩)
        (fun i => e ⟨i.val + 1, by omega⟩)
        (by
          intro i
          simpa using joins (⟨i.val + 1, by omega⟩ : Fin (n + 1)))

private theorem occurrencePathWalkAux_support {V : Type*} [Fintype V] (T : MGraph V)
    (S : SimpleGraph V) (hTS : graphSupport T = S) (hloop : Loopless T) :
    ∀ n (v : Fin (n + 1) → V) (e : Fin n → Occurrence T) (joins),
      (occurrencePathWalkAux T S hTS hloop n v e joins).support = List.ofFn v := by
  intro n
  induction n with
  | zero => intro v e joins; simp [occurrencePathWalkAux]
  | succ n ih =>
      intro v e joins
      simp only [occurrencePathWalkAux, SimpleGraph.Walk.support_cons, List.ofFn_succ]
      rw [ih (fun i => v ⟨i.val + 1, by omega⟩)
        (fun i => e ⟨i.val + 1, by omega⟩)
        (by
          intro i
          simpa using joins (⟨i.val + 1, by omega⟩ : Fin (n + 1)))]
      simp [List.ofFn_succ]
      funext i
      rfl

private theorem occurrencePathWalkAux_getVert {V : Type*} [Fintype V] (T : MGraph V)
    (S : SimpleGraph V) (hTS : graphSupport T = S) (hloop : Loopless T) :
    ∀ n (v : Fin (n + 1) → V) (e : Fin n → Occurrence T) (joins)
      (i : Fin (n + 1)),
      (occurrencePathWalkAux T S hTS hloop n v e joins).getVert i.val = v i := by
  intro n
  induction n with
  | zero =>
      intro v e joins i
      have hi : i = 0 := Fin.ext (by omega)
      rw [hi]
      simp [occurrencePathWalkAux]
  | succ n ih =>
      intro v e joins i
      by_cases hz : i.val = 0
      · have hi : i = ⟨0, by omega⟩ := Fin.ext hz
        rw [hi]
        simp [occurrencePathWalkAux]
      · let j : Fin (n + 1) := ⟨i.val - 1, by omega⟩
        have hi : i = ⟨j.val + 1, by omega⟩ := Fin.ext (by simp [j]; omega)
        rw [hi]
        simp only [occurrencePathWalkAux, SimpleGraph.Walk.getVert_cons_succ]
        exact ih (fun i => v ⟨i.val + 1, by omega⟩)
          (fun i => e ⟨i.val + 1, by omega⟩)
          (by
            intro i
            simpa using joins (⟨i.val + 1, by omega⟩ : Fin (n + 1))) j

private def occurrencePathWalk {V : Type*} [Fintype V] {T : MGraph V}
    {S : SimpleGraph V} (hTS : graphSupport T = S) (hloop : Loopless T)
    (p : OccurrencePath T) : S.Walk (p.vertex ⟨0, by omega⟩)
      (p.vertex ⟨p.length, by omega⟩) :=
  occurrencePathWalkAux T S hTS hloop p.length p.vertex p.edge p.joins

private theorem occurrencePathWalk_length {V : Type*} [Fintype V] {T : MGraph V}
    {S : SimpleGraph V} (hTS : graphSupport T = S) (hloop : Loopless T)
    (p : OccurrencePath T) : (occurrencePathWalk hTS hloop p).length = p.length :=
  occurrencePathWalkAux_length T S hTS hloop p.length p.vertex p.edge p.joins

private theorem occurrencePathWalk_support {V : Type*} [Fintype V] {T : MGraph V}
    {S : SimpleGraph V} (hTS : graphSupport T = S) (hloop : Loopless T)
    (p : OccurrencePath T) :
      (occurrencePathWalk hTS hloop p).support = List.ofFn p.vertex :=
  occurrencePathWalkAux_support T S hTS hloop p.length p.vertex p.edge p.joins

private theorem occurrencePathWalk_getVert {V : Type*} [Fintype V] {T : MGraph V}
    {S : SimpleGraph V} (hTS : graphSupport T = S) (hloop : Loopless T)
    (p : OccurrencePath T) (i : Fin (p.length + 1)) :
      (occurrencePathWalk hTS hloop p).getVert i.val = p.vertex i :=
  occurrencePathWalkAux_getVert T S hTS hloop p.length p.vertex p.edge p.joins i

private theorem occurrencePathWalk_isPath {V : Type*} [Fintype V] {T : MGraph V}
    {S : SimpleGraph V} (hTS : graphSupport T = S) (hloop : Loopless T)
    (p : OccurrencePath T) : (occurrencePathWalk hTS hloop p).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [occurrencePathWalk_support]
  exact List.nodup_ofFn.mpr p.vertex_injective

private def occurrencePathWalkAt {V : Type*} [Fintype V] {T : MGraph V}
    {S : SimpleGraph V} (hTS : graphSupport T = S) (hloop : Loopless T)
    {a b : V} (p : OccurrencePath T) (hp : PathFrom p a b) : S.Walk a b :=
  (occurrencePathWalk hTS hloop p).copy hp.1 hp.2

private theorem occurrencePathWalkAt_isPath {V : Type*} [Fintype V] {T : MGraph V}
    {S : SimpleGraph V} (hTS : graphSupport T = S) (hloop : Loopless T)
    {a b : V} (p : OccurrencePath T) (hp : PathFrom p a b) :
    (occurrencePathWalkAt hTS hloop p hp).IsPath := by
  change ((occurrencePathWalk hTS hloop p).copy hp.1 hp.2).IsPath
  exact (SimpleGraph.Walk.isPath_copy _ _ _).2 (occurrencePathWalk_isPath hTS hloop p)

private theorem occurrencePathWalkAt_length {V : Type*} [Fintype V] {T : MGraph V}
    {S : SimpleGraph V} (hTS : graphSupport T = S) (hloop : Loopless T)
    {a b : V} (p : OccurrencePath T) (hp : PathFrom p a b) :
    (occurrencePathWalkAt hTS hloop p hp).length = p.length := by
  change ((occurrencePathWalk hTS hloop p).copy hp.1 hp.2).length = p.length
  rw [SimpleGraph.Walk.length_copy]
  exact occurrencePathWalk_length hTS hloop p

private theorem occurrencePathWalkAt_getVert {V : Type*} [Fintype V] {T : MGraph V}
    {S : SimpleGraph V} (hTS : graphSupport T = S) (hloop : Loopless T)
    {a b : V} (p : OccurrencePath T) (hp : PathFrom p a b)
    (i : Fin (p.length + 1)) :
    (occurrencePathWalkAt hTS hloop p hp).getVert i.val = p.vertex i := by
  change ((occurrencePathWalk hTS hloop p).copy hp.1 hp.2).getVert i.val = p.vertex i
  rw [SimpleGraph.Walk.getVert_copy]
  exact occurrencePathWalk_getVert hTS hloop p i

private theorem treeMGraph_edge_positive {V : Type*} [Fintype V] (S : SimpleGraph V)
    {a b : V} (h : S.Adj a b) : 0 < treeMGraph S (s(a,b)) := by
  simp [treeMGraph, SimpleGraph.mem_edgeSet, h]

private def occurrencePathOfWalk {V : Type*} [Fintype V] {T : MGraph V}
    {S : SimpleGraph V} (hpos : ∀ {a b : V}, S.Adj a b → 0 < T (s(a,b)))
    {a b : V} (w : S.Walk a b) (hw : w.IsPath) : OccurrencePath T where
  length := w.length
  vertex := fun i => w.getVert i.val
  edge := fun i =>
    ⟨s(w.getVert i.val, w.getVert (i.val + 1)),
      ⟨0, hpos (w.adj_getVert_succ i.isLt)⟩⟩
  vertex_injective := by
    intro i j hij
    apply Fin.ext
    have hi : i.val < w.support.length := by rw [w.length_support]; exact i.isLt
    have hj : j.val < w.support.length := by rw [w.length_support]; exact j.isLt
    have hget : w.support[i.val]'hi = w.support[j.val]'hj := by
      simpa only [w.getVert_eq_support_getElem (Nat.le_of_lt_succ i.isLt),
        w.getVert_eq_support_getElem (Nat.le_of_lt_succ j.isLt)] using hij
    exact hw.support_nodup.getElem_inj_iff.mp hget
  edge_injective := by
    intro i j hij
    apply Fin.ext
    have hpair : s(w.getVert i.val, w.getVert (i.val + 1)) =
        s(w.getVert j.val, w.getVert (j.val + 1)) := congrArg Sigma.fst hij
    have hedge : w.edges[i.val] = w.edges[j.val] := by
      have hi : i.val < w.edges.length := by simpa using i.isLt
      have hj : j.val < w.edges.length := by simpa using j.isLt
      rw [w.getElem_edges hi, w.getElem_edges hj]
      exact hpair
    exact hw.edges_nodup.getElem_inj_iff.mp hedge
  joins := by
    intro i
    rfl

private theorem pathFrom_occurrencePathOfWalk {V : Type*} [Fintype V] {T : MGraph V}
    {S : SimpleGraph V} (hpos : ∀ {a b : V}, S.Adj a b → 0 < T (s(a,b)))
    {a b : V} (w : S.Walk a b) (hw : w.IsPath) :
    PathFrom (occurrencePathOfWalk hpos w hw) a b := by
  constructor <;> simp [occurrencePathOfWalk]

private theorem occurrence_eq_of_key_eq {V : Type*} [Fintype V] {T : MGraph V}
    (hTle : ∀ e, T e ≤ 1) (x y : Occurrence T) (hxy : x.1 = y.1) : x = y := by
  rcases x with ⟨x, ix⟩
  rcases y with ⟨y, iy⟩
  change x = y at hxy
  subst y
  have hpos : 0 < T x := lt_of_le_of_lt (Nat.zero_le _) ix.isLt
  have hmult := hTle x
  have hcount : T x = 1 := by omega
  have hfin : ix = iy := Fin.ext (by omega)
  cases hfin
  rfl

private theorem occurrencePath_eq_of_walkAt_eq {V : Type*} [Fintype V] {T : MGraph V}
    {S : SimpleGraph V} (hTS : graphSupport T = S) (hloop : Loopless T)
    (hTle : ∀ e, T e ≤ 1) {a b : V} (p p' : OccurrencePath T)
    (hp : PathFrom p a b) (hp' : PathFrom p' a b)
    (hwalk : occurrencePathWalkAt hTS hloop p hp = occurrencePathWalkAt hTS hloop p' hp') :
    p = p' := by
  cases p with
  | mk n v e hv he hj =>
    cases p' with
    | mk n' v' e' hv' he' hj' =>
      let P : OccurrencePath T := ⟨n, v, e, hv, he, hj⟩
      let Q : OccurrencePath T := ⟨n', v', e', hv', he', hj'⟩
      have hlen : n = n' := by
        have h := congrArg SimpleGraph.Walk.length hwalk
        rw [occurrencePathWalkAt_length hTS hloop P hp,
          occurrencePathWalkAt_length hTS hloop Q hp'] at h
        exact h
      cases hlen
      have hvertex : v = v' := by
        funext i
        have h := congrArg (fun w : S.Walk a b => w.getVert i.val) hwalk
        rw [occurrencePathWalkAt_getVert hTS hloop P hp i,
          occurrencePathWalkAt_getVert hTS hloop Q hp' i] at h
        exact h
      have hedge : e = e' := by
        funext i
        have hkey : (e i).1 = (e' i).1 := by
          calc
            (e i).1 = s(v ⟨i.val, by omega⟩, v ⟨i.val + 1, by omega⟩) := hj i
            _ = s(v' ⟨i.val, by omega⟩, v' ⟨i.val + 1, by omega⟩) := by rw [hvertex]
            _ = (e' i).1 := (hj' i).symm
        exact occurrence_eq_of_key_eq hTle (e i) (e' i) hkey
      rw [OccurrencePath.mk.injEq]
      exact ⟨rfl, heq_of_eq hvertex, heq_of_eq hedge⟩

theorem S3_55Statement_holds : S3_55Statement := by
  intro V _ hV K hK hconn
  let G := graphSupport K
  obtain ⟨S, hSG, hStree⟩ := hconn.exists_isTree_le
  let T := treeMGraph S
  have hTS : graphSupport T = S := by
    dsimp [T]
    exact graphSupport_treeMGraph S
  have hTloop : Loopless T := by
    dsimp [T]
    exact treeMGraph_loopless S
  have hsub : subgraph T K := by
    dsimp [T]
    exact treeMGraph_subgraph K S hSG
  have hTle : ∀ e, T e ≤ 1 := by
    intro e
    by_cases he : e ∈ S.edgeSet <;> simp [T, treeMGraph, he]
  have hspan : SpanningTree T K := by
    exact ⟨hTloop, hsub, hTle, by rw [hTS]; exact hStree⟩
  have hcount : edgeCount T + 1 = Fintype.card V := by
    rw [show T = treeMGraph S from rfl, edgeCount_treeMGraph]
    exact hStree.card_edgeFinset
  have hcolor : Colorable 2 T := by
    rcases hStree.colorable_two with ⟨c⟩
    refine ⟨c, ?_⟩
    intro a b hpos
    have hne : a ≠ b := by
      intro hab
      subst b
      rw [hTloop a] at hpos
      omega
    have hAdjT : (graphSupport T).Adj a b := ⟨hne, hpos⟩
    have hAdj : S.Adj a b := by rw [← hTS]; exact hAdjT
    simpa using c.map_rel hAdj
  have hpaths : ∀ a b : V, ∃! p : OccurrencePath T, PathFrom p a b := by
    intro a b
    obtain ⟨w, hw, huniq⟩ := hStree.existsUnique_path a b
    let p := occurrencePathOfWalk (fun h => treeMGraph_edge_positive S h) w hw
    have hp : PathFrom p a b := by
      exact pathFrom_occurrencePathOfWalk (fun h => treeMGraph_edge_positive S h) w hw
    refine ⟨p, hp, ?_⟩
    intro q hq
    have hqeq : occurrencePathWalkAt hTS hTloop q hq = w :=
      huniq (occurrencePathWalkAt hTS hTloop q hq)
        (occurrencePathWalkAt_isPath hTS hTloop q hq)
    have hpeq : occurrencePathWalkAt hTS hTloop p hp = w :=
      huniq (occurrencePathWalkAt hTS hTloop p hp)
        (occurrencePathWalkAt_isPath hTS hTloop p hp)
    exact (occurrencePath_eq_of_walkAt_eq hTS hTloop hTle p q hp hq
      (hpeq.trans hqeq.symm)).symm
  exact ⟨T, hspan, hcount, hcolor, hpaths⟩

end ThLean.W.S358
