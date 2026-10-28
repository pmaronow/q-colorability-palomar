import ThLean.BP.S3.Cycles

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S361
open ThresholdFoundations ThLean.BP.S3

variable {V : Type*} [Fintype V]

private def occPathOfWalk {T : MGraph V} {a b : V}
    (w : (graphSupport T).Walk a b) (hw : w.IsPath) (hm : ∀ e, T e ≤ 1) :
    OccurrencePath T := by
  classical
  let edgeFn : Fin w.length → Occurrence T := fun i =>
    let e := s(w.getVert i.val, w.getVert (i.val + 1))
    ⟨e, ⟨0, by
      have hadj := w.adj_getVert_succ i.isLt
      simpa [e, graphSupport] using hadj.2⟩⟩
  refine ⟨w.length, fun i => w.getVert i.val, edgeFn, ?_, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    have hi : i.val < w.support.length := by simpa using i.isLt
    have hj : j.val < w.support.length := by simpa using j.isLt
    have hget : w.support.get ⟨i.val, hi⟩ = w.support.get ⟨j.val, hj⟩ := by
      calc
        w.support.get ⟨i.val, hi⟩ = w.support[i.val]'hi := List.get_eq_getElem
        _ = w.getVert i.val := (w.getVert_eq_support_getElem (Nat.le_of_lt_succ i.isLt)).symm
        _ = w.getVert j.val := hij
        _ = w.support[j.val]'hj := w.getVert_eq_support_getElem (Nat.le_of_lt_succ j.isLt)
        _ = w.support.get ⟨j.val, hj⟩ :=
          (List.get_eq_getElem (l := w.support) (i := ⟨j.val, hj⟩)).symm
    have hidx := ((List.nodup_iff_injective_get).mp hw.2) hget
    exact congrArg (fun k : Fin w.support.length => k.val) hidx
  · intro i j hij
    apply Fin.ext
    have hpair : s(w.getVert i.val, w.getVert (i.val + 1)) =
        s(w.getVert j.val, w.getVert (j.val + 1)) := by
      change edgeFn i = edgeFn j at hij
      exact congrArg Sigma.fst hij
    have hget : w.edges.get ⟨i.val, by simpa using i.isLt⟩ =
        w.edges.get ⟨j.val, by simpa using j.isLt⟩ := by
      rw [List.get_eq_getElem, List.get_eq_getElem,
        w.getElem_edges (i := i.val) (by simpa using i.isLt),
        w.getElem_edges (i := j.val) (by simpa using j.isLt)]
      exact hpair
    have hidx := ((List.nodup_iff_injective_get).mp hw.1.1) hget
    exact congrArg (fun k : Fin w.edges.length => k.val) hidx
  · intro i
    change (edgeFn i).1 = _
    simp [edgeFn, w.getElem_edges (i := i.val) (by simpa using i.isLt)]

private theorem exists_occPath_of_spanningTree {T K : MGraph V}
    (hT : SpanningTree T K) (a b : V) :
    ∃ p : OccurrencePath T, PathFrom p a b := by
  obtain ⟨w, hw⟩ := hT.2.2.2.connected a b |>.exists_isPath
  refine ⟨occPathOfWalk w hw hT.2.2.1, ?_⟩
  constructor <;> simp [PathFrom, occPathOfWalk]

private theorem occLift_injective {T K : MGraph V} (h : subgraph T K) :
    Function.Injective (OccLift h) := by
  intro x y hxy
  cases x with
  | mk ex ix =>
    cases y with
    | mk ey iy =>
      have he : ex = ey := congrArg Sigma.fst hxy
      have hi : ix.val = iy.val := congrArg (fun z : Occurrence K => z.2.val) hxy
      subst ey
      have hix : ix = iy := Fin.ext hi
      cases hix
      rfl

private def closeTreePath {T K : MGraph V} (h : subgraph T K)
    {a b : V} (r : OccurrencePath T) (e : Occurrence K)
    (hpos : 1 ≤ r.length) (hp : PathFrom r a b)
    (hclose : e.1 = s(b,a))
    (hout : e ∉ Finset.univ.image (OccLift h)) : OccurrenceCycle K := by
  classical
  let efn : Fin (r.length + 1) → Occurrence K := fun i =>
    if hi : i.val < r.length then OccLift h (r.edge ⟨i.val, hi⟩) else e
  refine ⟨r.length + 1, by omega, r.vertex, efn, ?_, ?_, ?_⟩
  · exact r.vertex_injective
  · intro i j hij
    apply Fin.ext
    by_cases hi : i.val < r.length <;> by_cases hj : j.val < r.length
    · have hlift : OccLift h (r.edge ⟨i.val, hi⟩) =
          OccLift h (r.edge ⟨j.val, hj⟩) := by simpa [efn, hi, hj] using hij
      have heq := r.edge_injective (occLift_injective h hlift)
      exact congrArg (fun z : Fin r.length => z.val) heq
    · have hlift : OccLift h (r.edge ⟨i.val, hi⟩) = e := by
          simpa [efn, hi, hj] using hij
      exact False.elim (hout (Finset.mem_image.mpr
        ⟨r.edge ⟨i.val, hi⟩, Finset.mem_univ _, hlift⟩))
    · have hlift : OccLift h (r.edge ⟨j.val, hj⟩) = e := by
          simpa [efn, hi, hj] using hij.symm
      exact False.elim (hout (Finset.mem_image.mpr
        ⟨r.edge ⟨j.val, hj⟩, Finset.mem_univ _, hlift⟩))
    · have hi' : i.val = r.length := by omega
      have hj' : j.val = r.length := by omega
      exact hi'.trans hj'.symm
  · intro i
    by_cases hi : i.val < r.length
    · have hnext :
          (⟨(i.val + 1) % (r.length + 1), Nat.mod_lt _ (by omega)⟩ : Fin (r.length + 1)) =
          ⟨i.val + 1, Nat.succ_lt_succ hi⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt (Nat.succ_lt_succ hi)
      have hcur : i = (⟨i.val, Nat.lt_succ_of_lt hi⟩ : Fin (r.length + 1)) := Fin.ext rfl
      simp only [efn, dif_pos hi, OccLift]
      rw [r.joins ⟨i.val, hi⟩]
      have hv0 : r.vertex ⟨i.val, Nat.lt_succ_of_lt hi⟩ = r.vertex i :=
        congrArg r.vertex hcur.symm
      have hv1 : r.vertex ⟨i.val + 1, Nat.succ_lt_succ hi⟩ =
          r.vertex ⟨(i.val + 1) % (r.length + 1), Nat.mod_lt _ (by omega)⟩ :=
        congrArg r.vertex hnext.symm
      rw [hv0, hv1]
    · have hi' : i.val = r.length := by omega
      have heq : i = ⟨r.length, by omega⟩ := Fin.ext hi'
      let last : Fin (r.length + 1) := ⟨r.length, Nat.lt_succ_self _⟩
      have hlastEdge : efn last = e := by simp [efn, last]
      have hlastIdx :
          (⟨(r.length + 1) % (r.length + 1), Nat.mod_lt _ (by omega)⟩ : Fin (r.length + 1)) = 0 := by
        apply Fin.ext
        exact Nat.mod_self _
      rw [heq, hlastEdge, hlastIdx]
      rw [hclose, ← hp.2, ← hp.1]
      rfl

private theorem closeTreePath_diff {T K : MGraph V} (h : subgraph T K)
    {a b : V} (r : OccurrencePath T) (e : Occurrence K)
    (hpos : 1 ≤ r.length) (hp : PathFrom r a b)
    (hclose : e.1 = s(b,a))
    (hout : e ∉ Finset.univ.image (OccLift h)) :
    cycleOccurrences (closeTreePath h r e hpos hp hclose hout) \
      Finset.univ.image (OccLift h) = {e} := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxcyc, hxout⟩
    change x ∈ Finset.univ.image
      (fun i : Fin (r.length + 1) => (closeTreePath h r e hpos hp hclose hout).edge i) at hxcyc
    rcases Finset.mem_image.mp hxcyc with ⟨i, -, hxi⟩
    by_cases hi : i.val < r.length
    · have hxlift : OccLift h (r.edge ⟨i.val, hi⟩) = x := by
        simpa [closeTreePath, hi] using hxi
      exact False.elim (hxout (Finset.mem_image.mpr
        ⟨r.edge ⟨i.val, hi⟩, Finset.mem_univ _, hxlift⟩))
    · have hi' : i.val = r.length := by omega
      have hlast : i = ⟨r.length, Nat.lt_succ_self _⟩ := Fin.ext hi'
      have hxe : e = x := by simpa [closeTreePath, hi, hlast] using hxi
      exact Finset.mem_singleton.mpr hxe.symm
  · intro hx
    have hxe : x = e := Finset.mem_singleton.mp hx
    subst x
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hout⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨r.length, Nat.lt_succ_self _⟩, Finset.mem_univ _, ?_⟩
    simp [closeTreePath]

private theorem exists_fundamentalCycle {T K : MGraph V}
    (hK : Loopless K) (hT : SpanningTree T K) (h : subgraph T K)
    (e : Occurrence K) (hout : e ∉ Finset.univ.image (OccLift h)) :
    ∃ c : OccurrenceCycle K,
      cycleOccurrences c \ Finset.univ.image (OccLift h) = {e} := by
  classical
  have hex : ∃ a b : V, e.1 = s(a,b) :=
    Sym2.inductionOn e.1 (fun a b => ⟨a, b, rfl⟩)
  rcases hex with ⟨a, b, hpair⟩
  have hepos : 0 < K (s(a,b)) := by
    have hpos : 0 < K e.1 := Nat.lt_of_le_of_lt (Nat.zero_le _) e.2.isLt
    simpa [hpair] using hpos
  have hab : a ≠ b := by
    intro hab
    subst b
    have hzero := hK a
    omega
  obtain ⟨r, hr⟩ := exists_occPath_of_spanningTree hT a b
  have hrpos : 1 ≤ r.length := by
    by_contra hn
    have hz : r.length = 0 := by omega
    have hidx : (0 : Fin (r.length + 1)) = ⟨r.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      omega
    have hab' : a = b := by
      calc
        a = r.vertex 0 := hr.1.symm
        _ = r.vertex ⟨r.length, Nat.lt_succ_self _⟩ := congrArg r.vertex hidx
        _ = b := hr.2
    exact hab hab'
  have hclose : e.1 = s(b,a) := by
    rw [hpair]
    exact Sym2.eq_swap
  exact ⟨closeTreePath h r e hrpos hr hclose hout,
    closeTreePath_diff h r e hrpos hr hclose hout⟩

theorem S3_58Statement_holds : ThLean.BP.S3.S3_58Statement := by
  intro V _ K T hK hT h p p' hne hpout hp'out
  obtain ⟨c, hc⟩ := exists_fundamentalCycle hK hT h p hpout
  obtain ⟨d, hd⟩ := exists_fundamentalCycle hK hT h p' hp'out
  refine ⟨c, d, hc, hd, ?_⟩
  intro hp'c
  have hp'diff : p' ∈ cycleOccurrences c \ Finset.univ.image (OccLift h) :=
    Finset.mem_sdiff.mpr ⟨hp'c, hp'out⟩
  rw [hc] at hp'diff
  exact hne (Finset.mem_singleton.mp hp'diff).symm

end ThLean.W.S361
