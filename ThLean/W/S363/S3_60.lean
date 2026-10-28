import ThLean.W.S363.Rotate

set_option maxHeartbeats 1000000

universe u

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ThLean.W.S363
open ThresholdFoundations

private theorem cycle_edge_endpoints {V : Type u} [Fintype V] {G : MGraph V}
    (c : OccurrenceCycle G) (o : Occurrence G) (ho : o ∈ cycleOccurrences c)
    (x y : V) (hpair : o.1 = s(x, y)) :
    x ∈ cycleVertices c ∧ y ∈ cycleVertices c := by
  classical
  letI : NeZero c.length := ⟨by
    have hc := c.length_ge_two
    omega⟩
  rcases (by simpa [cycleOccurrences] using ho) with ⟨i, hEdge⟩
  have hnext := nextIndex_eq i
  have hpair' : s(x, y) = s(c.vertex i, c.vertex (nextIndex i)) := by
    calc
      s(x, y) = o.1 := hpair.symm
      _ = (c.edge i).1 := (congrArg Sigma.fst hEdge).symm
      _ = s(c.vertex i, c.vertex (nextIndex i)) := by
        rw [hnext]
        exact c.joins i
  rcases Sym2.eq_iff.mp hpair' with h | h
  · rcases h with ⟨hx, hy⟩
    constructor
    · simpa [cycleVertices] using
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hx.symm⟩)
    · simpa [cycleVertices] using
        (Finset.mem_image.mpr ⟨nextIndex i, Finset.mem_univ _, hy.symm⟩)
  · rcases h with ⟨hx, hy⟩
    constructor
    · simpa [cycleVertices] using
        (Finset.mem_image.mpr ⟨nextIndex i, Finset.mem_univ _, hx.symm⟩)
    · simpa [cycleVertices] using
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hy.symm⟩)

theorem S3_60Statement_holds : ThLean.BP.S3.S3_60Statement := by
  intro V inst G c d e he hne hcard
  let n0 : ℕ := d.length
  letI : NeZero n0 := ⟨by
    dsimp [n0]
    have hc := d.length_ge_two
    omega⟩
  rcases (by simpa [cycleOccurrences] using he) with ⟨j, hje⟩
  let last0 : Fin n0 := ⟨n0 - 1, by dsimp [n0]; have hc := d.length_ge_two; omega⟩
  let rot : Fin n0 := j - last0
  have hrotlast : finCycle rot last0 = j := by
    have h := rotate_last_to d j
    simpa [rot, last0, n0] using h
  let d0 : OccurrenceCycle G := rotateCycle d rot
  have hd0len : d0.length = n0 := by
    simpa [d0, n0] using rotateCycle_length d rot
  have hd0ge2 : 2 ≤ d0.length := by
    rw [hd0len]
    dsimp [n0]
    exact d.length_ge_two
  letI : NeZero d0.length := ⟨by omega⟩
  let last : Fin d0.length := ⟨d0.length - 1, by have := hd0ge2; omega⟩
  have hlastEq : last = last0 := by
    apply Fin.ext
    dsimp [last, last0, n0, d0, rotateCycle]
  have hd0last : d0.edge last = e := by
    change d.edge (finCycle rot last) = e
    rw [hlastEq, hrotlast, hje]
  have hd0vertices : cycleVertices d0 = cycleVertices d :=
    rotate_cycleVertices d rot
  have hd0occurrences : cycleOccurrences d0 = cycleOccurrences d :=
    rotate_cycleOccurrences d rot
  have hcard0 : 1 < (cycleVertices c ∩ cycleVertices d0).card := by
    calc
      1 < (cycleVertices c ∩ cycleVertices d).card :=
        Nat.lt_of_lt_of_le (by decide : 1 < 2) hcard
      _ = (cycleVertices c ∩ cycleVertices d0).card := by rw [hd0vertices]
  rcases Finset.one_lt_card_iff.mp hcard0 with
    ⟨x, y, hxy1, hxy2, hxy⟩
  have hxI := Finset.mem_inter.mp hxy1
  have hyI := Finset.mem_inter.mp hxy2
  have hxD0 : x ∈ cycleVertices d0 := hxI.2
  have hyD0 : y ∈ cycleVertices d0 := hyI.2
  rcases (by simpa [cycleVertices] using hxD0) with ⟨ix, hxv⟩
  rcases (by simpa [cycleVertices] using hyD0) with ⟨iy, hyv⟩
  have hixneiy : ix ≠ iy := by
    intro h
    apply hxy
    calc
      x = d0.vertex ix := hxv.symm
      _ = d0.vertex iy := congrArg d0.vertex h
      _ = y := hyv
  let H : Finset (Fin d0.length) := Finset.univ.filter
    (fun i => d0.vertex i ∈ cycleVertices c)
  have hixH : ix ∈ H := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · change d0.vertex ix ∈ cycleVertices c
      rw [hxv]
      exact hxI.1
  have hiyH : iy ∈ H := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · change d0.vertex iy ∈ cycleVertices c
      rw [hyv]
      exact hyI.1
  have hHne : H.Nonempty := ⟨ix, hixH⟩
  let lo : Fin d0.length := H.min' hHne
  let hi : Fin d0.length := H.max' hHne
  have hloH : lo ∈ H := by
    dsimp [lo]
    exact Finset.min'_mem H hHne
  have hhiH : hi ∈ H := by
    dsimp [hi]
    exact Finset.max'_mem H hHne
  have hlohi : lo < hi := by
    apply lt_of_le_of_ne (Finset.min'_le H hi hhiH)
    intro heq
    have hixhi : ix ≤ hi := Finset.le_max' H ix hixH
    have hiyhi : iy ≤ hi := Finset.le_max' H iy hiyH
    have hixlo : lo ≤ ix := Finset.min'_le H ix hixH
    have hiylo : lo ≤ iy := Finset.min'_le H iy hiyH
    have hixle : ix ≤ lo := by rw [← heq] at hixhi; exact hixhi
    have hiyLe : iy ≤ lo := by rw [← heq] at hiyhi; exact hiyhi
    have hixEq : ix = lo := le_antisymm hixle hixlo
    have hiyEq : iy = lo := le_antisymm hiyLe hiylo
    exact hixneiy (hixEq.trans hiyEq.symm)
  have hlohiVal : lo.val < hi.val := Fin.lt_def.mp hlohi
  have hloC : d0.vertex lo ∈ cycleVertices c :=
    (Finset.mem_filter.mp hloH).2
  have hhiC : d0.vertex hi ∈ cycleVertices c :=
    (Finset.mem_filter.mp hhiH).2
  let L : ℕ := d0.length - hi.val + lo.val
  have hloLt : lo.val < d0.length := lo.isLt
  have hhiLt : hi.val < d0.length := hi.isLt
  have hLpos : 0 < L := by
    dsimp [L]
    have hlohi' : lo.val < hi.val := hlohiVal
    omega
  have hLlt : L < d0.length := by
    dsimp [L]
    have hlohi' : lo.val < hi.val := hlohiVal
    omega
  have hsum : L + hi.val = d0.length + lo.val := by
    dsimp [L]
    omega
  let idxL : Fin d0.length := ⟨L, hLlt⟩
  let idx0 : Fin d0.length := ⟨0, by omega⟩
  have hEndIdx : finCycle hi idxL = lo := by
    apply Fin.ext
    have hval : (finCycle hi idxL).val = (L + hi.val) % d0.length := by
      simp [finCycle_apply, Fin.add_def, idxL]
    rw [hval, hsum]
    simp [Nat.add_mod, Nat.mod_eq_of_lt lo.isLt]
  have hzeroIdx : finCycle hi idx0 = hi := by
    apply Fin.ext
    simp [idx0, finCycle_apply, Fin.add_def]
  have noCInterior (k : Fin d0.length) (hk0 : 0 < k.val) (hkL : k.val < L) :
      d0.vertex (finCycle hi k) ∉ cycleVertices c := by
    intro hkc
    have hH : finCycle hi k ∈ H := by
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · change d0.vertex (finCycle hi k) ∈ cycleVertices c
        exact hkc
    have hval : (finCycle hi k).val = (hi.val + k.val) % d0.length := by
      simp [finCycle_apply, Fin.add_def, Nat.add_comm]
    by_cases hsumlt : hi.val + k.val < d0.length
    · rw [Nat.mod_eq_of_lt hsumlt] at hval
      have hgt : hi < finCycle hi k := by
        apply Fin.lt_def.mpr
        rw [hval]
        omega
      exact (not_le_of_gt hgt) (Finset.le_max' H (finCycle hi k) hH)
    · have hsumhi : hi.val + k.val < d0.length + lo.val := by
        dsimp [L] at hkL
        have hhi := hi.isLt
        have hlo := lo.isLt
        omega
      have hsublt : hi.val + k.val - d0.length < d0.length := by omega
      have hsumEq : hi.val + k.val = d0.length + (hi.val + k.val - d0.length) := by omega
      have hmod : (hi.val + k.val) % d0.length = hi.val + k.val - d0.length := by
        rw [hsumEq]
        simp [Nat.add_mod, Nat.mod_eq_of_lt hsublt]
      rw [hmod] at hval
      have hlt : finCycle hi k < lo := by
        apply Fin.lt_def.mpr
        rw [hval]
        omega
      exact (not_le_of_gt hlt) (Finset.min'_le H (finCycle hi k) hH)
  let idxV : Fin (L + 1) → Fin d0.length := fun i => ⟨i.val, by omega⟩
  let idxE : Fin L → Fin d0.length := fun i => ⟨i.val, by omega⟩
  let p : OccurrencePath G := {
    length := L
    vertex := fun i => d0.vertex (finCycle hi (idxV i))
    edge := fun i => d0.edge (finCycle hi (idxE i))
    vertex_injective := by
      intro i j hij
      have hshift : finCycle hi (idxV i) = finCycle hi (idxV j) :=
        d0.vertex_injective (by simpa [idxV] using hij)
      have hidx : idxV i = idxV j := (finCycle hi).injective hshift
      apply Fin.ext
      have hv := congrArg Fin.val hidx
      simpa [idxV] using hv
    edge_injective := by
      intro i j hij
      have hshift : finCycle hi (idxE i) = finCycle hi (idxE j) :=
        d0.edge_injective (by simpa [idxE] using hij)
      have hidx : idxE i = idxE j := (finCycle hi).injective hshift
      apply Fin.ext
      have hv := congrArg Fin.val hidx
      simpa [idxE] using hv
    joins := by
      intro i
      let k : Fin d0.length := idxE i
      have hIPlus : i.val + 1 < d0.length := by
        have hi := i.isLt
        omega
      have hnext : nextIndex k = idxV ⟨i.val + 1, by omega⟩ := by
        apply Fin.ext
        simp [nextIndex, idxV, idxE, k, Fin.add_def, Nat.mod_eq_of_lt hIPlus]
      have hshiftNext : nextIndex (finCycle hi k) =
          finCycle hi (idxV ⟨i.val + 1, by omega⟩) := by
        calc
          nextIndex (finCycle hi k) = finCycle hi (nextIndex k) :=
            (finCycle_next hi k).symm
          _ = finCycle hi (idxV ⟨i.val + 1, by omega⟩) :=
            congrArg (finCycle hi) hnext
      change (d0.edge (finCycle hi k)).1 =
        s(d0.vertex (finCycle hi (idxV ⟨i.val, by omega⟩)),
          d0.vertex (finCycle hi (idxV ⟨i.val + 1, by omega⟩)))
      rw [d0.joins (finCycle hi k)]
      congr 2
      rw [← nextIndex_eq (finCycle hi k)]
      exact hshiftNext }
  have hPathFrom : PathFrom p (d0.vertex hi) (d0.vertex lo) := by
    constructor
    · change d0.vertex (finCycle hi idx0) = d0.vertex hi
      rw [hzeroIdx]
    · change d0.vertex (finCycle hi idxL) = d0.vertex lo
      rw [hEndIdx]
  have hPathLength : 1 ≤ p.length := by
    dsimp [p]
    omega
  have hEndpointsNe : d0.vertex hi ≠ d0.vertex lo := by
    intro heq
    exact (ne_of_gt hlohi) (d0.vertex_injective heq)
  have hPathVertices :
      pathVertices p ∩ cycleVertices c = {d0.vertex hi, d0.vertex lo} := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_inter.mp hz with ⟨hzp, hzc⟩
      rcases (by simpa [pathVertices] using hzp) with ⟨t, htz⟩
      by_cases ht0 : t.val = 0
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        left
        have ht : t = (⟨0, by omega⟩ : Fin (L + 1)) := Fin.ext ht0
        have hta : p.vertex t = d0.vertex hi := by
          rw [ht]
          change d0.vertex (finCycle hi idx0) = d0.vertex hi
          rw [hzeroIdx]
        exact htz.symm.trans hta
      · by_cases htL : t.val = L
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          right
          have ht : t = (⟨L, by omega⟩ : Fin (L + 1)) := Fin.ext htL
          have htb : p.vertex t = d0.vertex lo := by
            rw [ht]
            change d0.vertex (finCycle hi idxL) = d0.vertex lo
            rw [hEndIdx]
          exact htz.symm.trans htb
        · have htpos : 0 < t.val := by omega
          have htbound : t.val < L + 1 := by simpa [p] using t.isLt
          have htlt : t.val < L := by omega
          have hnot := noCInterior (idxV t) (by simp [idxV, htpos])
            (by simp [idxV, htlt])
          have htinC : p.vertex t ∈ cycleVertices c := by rw [htz]; exact hzc
          have htinC' : d0.vertex (finCycle hi (idxV t)) ∈ cycleVertices c := by
            simpa [p] using htinC
          exact False.elim (hnot htinC')
    · intro hz
      rcases Finset.mem_insert.mp hz with hza | hzb
      · subst z
        apply Finset.mem_inter.mpr
        constructor
        · change d0.vertex hi ∈ Finset.univ.image p.vertex
          apply Finset.mem_image.mpr
          refine ⟨(⟨0, by omega⟩ : Fin (L + 1)), Finset.mem_univ _, ?_⟩
          change d0.vertex (finCycle hi idx0) = d0.vertex hi
          rw [hzeroIdx]
        · exact hhiC
      · have hzb' : z = d0.vertex lo := Finset.mem_singleton.mp hzb
        subst z
        apply Finset.mem_inter.mpr
        constructor
        · change d0.vertex lo ∈ Finset.univ.image p.vertex
          apply Finset.mem_image.mpr
          refine ⟨(⟨L, by omega⟩ : Fin (L + 1)), Finset.mem_univ _, ?_⟩
          change d0.vertex (finCycle hi idxL) = d0.vertex lo
          rw [hEndIdx]
        · exact hloC
  let eIdxNat : ℕ := d0.length - 1 - hi.val
  have heIdxLt : eIdxNat < L := by
    dsimp [eIdxNat, L]
    omega
  let eIdx : Fin L := ⟨eIdxNat, heIdxLt⟩
  let eIdxCycle : Fin d0.length := idxE eIdx
  have heIdxSum : eIdxNat + hi.val = d0.length - 1 := by
    dsimp [eIdxNat]
    omega
  have heIdxEq : finCycle hi eIdxCycle = last := by
    apply Fin.ext
    have hval : (finCycle hi eIdxCycle).val = (eIdxNat + hi.val) % d0.length := by
      change (eIdxCycle + hi).val = (eIdxNat + hi.val) % d0.length
      rw [Fin.add_def]
    rw [hval, heIdxSum]
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_lt_of_le (by omega) (Nat.le_refl _)
  have heEdge : p.edge eIdx = e := by
    change d0.edge (finCycle hi (idxE eIdx)) = e
    rw [heIdxEq]
    exact hd0last
  have hePath : e ∈ pathOccurrences p := by
    change e ∈ Finset.univ.image p.edge
    exact Finset.mem_image.mpr ⟨eIdx, Finset.mem_univ _, heEdge⟩
  have hPathOccurrences : pathOccurrences p ⊆ cycleOccurrences d := by
    intro o ho
    rcases (by simpa [pathOccurrences] using ho) with ⟨i, hio⟩
    have hmem : d0.edge (finCycle hi (idxE i)) ∈ cycleOccurrences d0 := by
      change d0.edge (finCycle hi (idxE i)) ∈ Finset.univ.image d0.edge
      exact Finset.mem_image.mpr ⟨finCycle hi (idxE i), Finset.mem_univ _, rfl⟩
    rw [← hio]
    change d0.edge (finCycle hi (idxE i)) ∈ cycleOccurrences d
    rw [← hd0occurrences]
    exact hmem
  have hDisjoint : Disjoint (pathOccurrences p) (cycleOccurrences c) := by
    apply Finset.disjoint_left.mpr
    intro o ho
    intro hoc
    rcases (by simpa [pathOccurrences] using ho) with ⟨i, hio⟩
    let k : Fin d0.length := idxE i
    have hpair : o.1 = s(d0.vertex (finCycle hi k),
        d0.vertex (nextIndex (finCycle hi k))) := by
      calc
        o.1 = (d0.edge (finCycle hi k)).1 := by
          calc
            o.1 = (p.edge i).1 := congrArg Sigma.fst hio.symm
            _ = (d0.edge (finCycle hi k)).1 := rfl
        _ = s(d0.vertex (finCycle hi k), d0.vertex (nextIndex (finCycle hi k))) := by
          rw [d0.joins (finCycle hi k), nextIndex_eq (finCycle hi k)]
    have hends := cycle_edge_endpoints c o hoc _ _ hpair
    by_cases hi0 : i.val = 0
    · by_cases hLone : L = 1
      · have hie : i = eIdx := by
          apply Fin.ext
          dsimp [eIdx, eIdxNat]
          omega
        have hoe : o = e := by
          calc
            o = p.edge i := hio.symm
            _ = p.edge eIdx := congrArg p.edge hie
            _ = e := heEdge
        exact hne (by simpa [hoe] using hoc)
      · have hLbig : 1 < L := by omega
        have hkval : k.val = 0 := by simpa [k, idxE] using hi0
        have hv : (nextIndex k).val = 1 := by
          have hraw := congrArg Fin.val (nextIndex_eq k)
          have hraw' : (nextIndex k).val = (k.val + 1) % d0.length := by simpa using hraw
          rw [hraw', hkval]
          exact Nat.mod_eq_of_lt (by omega)
        have hpos : 0 < (nextIndex k).val := by
          rw [hv]
          omega
        have hlt : (nextIndex k).val < L := by
          rw [hv]
          exact hLbig
        have hshiftNext : finCycle hi (nextIndex k) = nextIndex (finCycle hi k) :=
          finCycle_next hi k
        have hnextC : d0.vertex (finCycle hi (nextIndex k)) ∈ cycleVertices c := by
          rw [hshiftNext]
          exact hends.2
        exact noCInterior (nextIndex k) hpos hlt hnextC
    · have hpos : 0 < k.val := by simp [k, idxE]; omega
      have hlt : k.val < L := by simpa [k, idxE] using i.isLt
      exact noCInterior k hpos hlt hends.1
  exact ⟨p, d0.vertex hi, d0.vertex lo,
    hPathLength, hEndpointsNe, hPathFrom, hhiC, hloC,
    hPathVertices, hPathOccurrences, hePath, hDisjoint⟩

end ThLean.W.S363
